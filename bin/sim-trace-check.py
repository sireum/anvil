#!/usr/bin/env python3
"""
sim-trace-check.py — verify Anvil-generated hardware against the IR simulator.

For each generated project under jvm/result, this script:
  1. generates the FPGA Verilog via sbt if it is missing;
  2. instruments chisel/generated_verilog/fpgaTb.v with a per-IP CP-register
     monitor (BLKTRACE lines) and the TopCP execution-cycle counter
     (same counter as the HLS_paper_experiment flow); the original testbench
     is kept as fpgaTb.v.orig;
  3. runs the project's own fpgaTestbenchScript.tcl in Vivado batch mode and
     launches a headless ModelSim simulation;
  4. extracts the executed (procedure, block) sequence from simulate.log and
     compares it, event by event, against the "Evaluating <proc> block .N"
     sequence in the matching jvm/result-sim/<bench>.sc (...)/output.txt
     produced by IRSimulatorTest.

The hardware is reported PASS when the first testbench run executes exactly
the same block sequence as the IR simulator (the generated testbench starts
the design twice; the second run is reported informationally).

Usage:
  bin/sim-trace-check.py [options] [project-dir ...]
    (no project-dir: all directories under jvm/result)

Options:
  --skip-sim      reuse an existing vivado_project/.../simulate.log
  --keep-project  do not delete vivado_project before re-running

Environment overrides:
  VIVADO_BIN       (default /home/kejun/software/vivado_2024_2/Vivado/2024.2/bin/vivado)
  MODELSIM_DIR     (default /home/kejun/software/modelsim/modeltech/linux_x86_64)
  SBT_BIN          (default <repo>/bin/sbt/bin/sbt)
  SBT_JAVA_HOME    JDK for sbt/Chisel; needs Java 8-17 for Scala 2.13.10
                   (default /home/kejun/.sdkman/candidates/java/8.0.472-amzn)

Prerequisite: the golden traces must be up to date with the current example
sources — regenerate them with:
  sireum proyek test --classes org.sireum.anvil.IRSimulatorTest <kekinian-dir>
"""

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys

ANVIL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULT = os.path.join(ANVIL, "jvm", "result")
RESULT_SIM = os.path.join(ANVIL, "jvm", "result-sim")

VIVADO_BIN = os.environ.get(
    "VIVADO_BIN", "/home/kejun/software/vivado_2024_2/Vivado/2024.2/bin/vivado")
MODELSIM_DIR = os.environ.get(
    "MODELSIM_DIR", "/home/kejun/software/modelsim/modeltech/linux_x86_64")
SBT_BIN = os.environ.get(
    "SBT_BIN", os.path.join(os.path.dirname(ANVIL), "bin", "sbt", "bin", "sbt"))
SBT_JAVA_HOME = os.environ.get(
    "SBT_JAVA_HOME", "/home/kejun/.sdkman/candidates/java/8.0.472-amzn")

MARKER = "BLKTRACE"
DISP_MARKER = "DISPTRACE"
BM_PATH = "u_Top.arbBlockMemoryWrapper.mod"


def canon(name):
    """Canonical procedure name shared by golden trace and RTL labels.

    Golden names like "DLLPool.<init>" and RTL labels like "DLLPool_init_"
    must compare equal, so strip everything but alphanumerics. An optional
    trailing "_object" (RTL object-method suffix) is dropped first.
    """
    if name.endswith("_object"):
        name = name[:-len("_object")]
    return re.sub(r"[^0-9A-Za-z]", "", name)


def project_name(proj_dir):
    """Vivado project name, e.g. BubbleTest, from fpgaTestbenchScript.tcl."""
    tcl = os.path.join(proj_dir, "fpgaTestbenchScript.tcl")
    with open(tcl) as f:
        m = re.search(r"create_project\s+(\w+)", f.read())
    if not m:
        raise RuntimeError(f"cannot find create_project in {tcl}")
    return m.group(1)


def golden_path(proj_dir):
    base = os.path.basename(proj_dir.rstrip("/"))
    bench = base.split("_sc_")[0]
    tg = ", temp-global" if "temp-global" in base else ""
    return os.path.join(
        RESULT_SIM, f"{bench}.sc (split-temp, temp-local{tg}, with-mem-ip)", "output.txt")


def load_golden(path):
    seq = []
    rx = re.compile(r"^Evaluating (\S+) block \.(\d+) ")
    with open(path) as f:
        for line in f:
            m = rx.match(line)
            if m:
                seq.append((canon(m.group(1)), int(m.group(2))))
    return seq


def ip_instances(proj_dir):
    """(verilog_instance, verilog_cp_reg, label) for every IP in FPGATop.scala."""
    src = os.path.join(proj_dir, "chisel", "src", "main", "scala", "FPGATop.scala")
    insts = []
    with open(src) as f:
        for m in re.finditer(r"val mod_(\S+) = withReset", f.read()):
            base = m.group(1).replace("$", "")  # firrtl drops '$'
            label = base[:-len("_object")] if base.endswith("_object") else base
            insts.append((f"mod_{base}", f"{base}CP", label))
    if not insts:
        raise RuntimeError(f"no IP instances found in {src}")
    return insts


def is_bram_native(proj_dir):
    try:
        with open(os.path.join(proj_dir, "config.txt")) as f:
            return "BramNative" in f.read()
    except OSError:
        return False


def instrument_tb(proj_dir):
    tb = os.path.join(proj_dir, "chisel", "generated_verilog", "fpgaTb.v")
    with open(tb) as f:
        text = f.read()
    if MARKER in text and (DISP_MARKER in text or not is_bram_native(proj_dir)):
        return False  # already instrumented with the current version
    if MARKER in text:
        # older instrumentation version: restart from the pristine testbench
        with open(tb + ".orig") as f:
            text = f.read()
    insts = ip_instances(proj_dir)
    lines = [
        "",
        "  // ---- TopCP first-run execution-cycle counter (auto-inserted) ----",
        "  integer exec_cyc = 0;",
        "  reg exec_started = 1'b0;",
        "  reg exec_reported = 1'b0;",
        "  always @(posedge clk) begin",
        "    if (u_Top.TopCP == 4'd2) begin",
        "      exec_started <= 1'b1;",
        "      if (!exec_reported) exec_cyc <= exec_cyc + 1;",
        "    end",
        "    if (exec_started && !exec_reported && (u_Top.TopCP != 4'd2)) begin",
        "      exec_reported <= 1'b1;",
        '      $display("ANVIL_EXEC_CYCLES=%0d (exit state=%0d)", exec_cyc, u_Top.TopCP);',
        "    end",
        "  end",
        "",
        "  // ---- BLKTRACE: per-IP CP change monitor (auto-inserted) ----",
    ]
    regs = [f"bt_p{i}" for i in range(len(insts))]
    lines.append("  reg [15:0] " + ", ".join(regs) + ";")
    lines.append("  initial begin " + " ".join(f"{r} = 16'hFFFF;" for r in regs) + " end")
    lines.append("  always @(posedge clk) begin")
    for (inst, cp, label), r in zip(insts, regs):
        sig = f"u_Top.{inst}.{cp}"
        lines.append(f"    if ({sig} !== {r}) begin")
        lines.append(f"      {r} <= {sig};")
        lines.append(f'      $display("{MARKER} %0t {label} %0d", $time, {sig});')
        lines.append("    end")
    lines.append("  end")
    if is_bram_native(proj_dir):
        lines += [
            "",
            "  // ---- DISPTRACE: BlockMemory write-port monitor (auto-inserted) ----",
            "  reg dt_prev;",
            "  initial dt_prev = 1'b0;",
            "  always @(posedge clk) begin",
            f"    if ({BM_PATH}.io_writeValid && !dt_prev) begin",
            f'      $display("{DISP_MARKER} %0t %0d %0d %h", $time,',
            f"        {BM_PATH}.io_writeAddr + {BM_PATH}.io_writeOffset,",
            f"        {BM_PATH}.io_writeLen, {BM_PATH}.io_writeData);",
            "    end",
            f"    dt_prev <= {BM_PATH}.io_writeValid;",
            "  end",
        ]
    lines.append("  // ---- end auto-inserted instrumentation ----")
    lines.append("")
    if not os.path.exists(tb + ".orig"):
        shutil.copyfile(tb, tb + ".orig")
    with open(tb, "w") as f:
        f.write(text.replace("\nendmodule", "\n" + "\n".join(lines) + "\nendmodule", 1))
    return True


def ensure_fpga_verilog(proj_dir, proj):
    v = os.path.join(proj_dir, "chisel", "generated_verilog", f"FPGA{proj}", f"{proj}.v")
    src = os.path.join(proj_dir, "chisel", "src", "main", "scala", "FPGATop.scala")
    if os.path.isfile(v):
        if not os.path.isfile(src) or os.path.getmtime(v) >= os.path.getmtime(src):
            return
        print("  FPGA Verilog is older than the Chisel sources; regenerating ...")
    print(f"  FPGA Verilog missing; running sbt Test/runMain FPGA{proj}VerilogGeneration ...")
    env = dict(os.environ)
    if os.path.isdir(SBT_JAVA_HOME):
        env["JAVA_HOME"] = SBT_JAVA_HOME
        env["PATH"] = os.path.join(SBT_JAVA_HOME, "bin") + os.pathsep + env.get("PATH", "")
    subprocess.run(
        [SBT_BIN, "-J-Xss32m", f"Test/runMain FPGA{proj}VerilogGeneration"],
        cwd=os.path.join(proj_dir, "chisel"), env=env, check=True, timeout=1800)
    if not os.path.isfile(v):
        raise RuntimeError(f"sbt finished but {v} still missing")


def run_simulation(proj_dir, keep_project):
    if not keep_project:
        shutil.rmtree(os.path.join(proj_dir, "vivado_project"), ignore_errors=True)
    tcl = os.path.join(proj_dir, "_simcheck.tcl")
    with open(tcl, "w") as f:
        f.write("source ./fpgaTestbenchScript.tcl\n"
                f"launch_simulation -install_path {MODELSIM_DIR}\n"
                "exit\n")
    env = dict(os.environ)
    env["PATH"] = os.path.dirname(VIVADO_BIN) + os.pathsep + MODELSIM_DIR + os.pathsep + env["PATH"]
    r = subprocess.run(
        [VIVADO_BIN, "-mode", "batch", "-nojournal",
         "-log", "vivado_simcheck.log", "-source", "_simcheck.tcl"],
        cwd=proj_dir, env=env, timeout=3600,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if r.returncode != 0:
        print(f"  WARNING: vivado exited with {r.returncode} (see vivado_simcheck.log)")


def find_simulate_log(proj_dir):
    logs = glob.glob(os.path.join(
        proj_dir, "vivado_project", "*.sim", "sim_1", "behav", "modelsim", "simulate.log"))
    return logs[0] if logs else None


def real_block_map(proj_dir):
    """canon(proc) -> set of real IR block numbers, from the generated ip_func
    sources. CP values outside this set are synthetic states (e.g. the
    register-restore state used on recursive returns) with no counterpart in
    the IR simulator trace, and must be filtered out before comparing."""
    blocks = {}
    for f in glob.glob(os.path.join(proj_dir, "chisel", "src", "main", "scala", "ip_func_*.scala")):
        with open(f, errors="replace") as fh:
            text = fh.read()
        m = re.search(r"\nclass (\S+) \(", text)
        if not m:
            continue
        key = canon(m.group(1))
        blocks[key] = {int(n) for n in re.findall(r"_Block_(\d+)\b", text)}
    return blocks


def load_rtl(sim_log, block_map=None):
    events, cycles, disp = [], [], []
    rx = re.compile(rf"{MARKER} (\d+) (\S+) (\d+)\b")
    dx = re.compile(rf"{DISP_MARKER} (\d+) (\d+) (\d+) ([0-9a-fA-Fx]+)")
    cyc = re.compile(r"ANVIL_EXEC_CYCLES=(\d+) \(exit state=(\d+)\)")
    with open(sim_log, errors="replace") as f:
        for line in f:
            m = rx.search(line)
            if m:
                t, proc, cp = int(m.group(1)), canon(m.group(2)), int(m.group(3))
                if cp < 3:  # CP 0/1/2 are halt/idle states, not IR blocks
                    continue
                if block_map is not None and proc in block_map and cp not in block_map[proc]:
                    continue  # synthetic state (e.g. recursive-return restore)
                events.append((t, proc, cp))
                continue
            m = dx.search(line)
            if m:
                if "x" not in m.group(4) and "X" not in m.group(4):
                    disp.append((int(m.group(1)), int(m.group(2)),
                                 int(m.group(3)), int(m.group(4), 16)))
                continue
            m = cyc.search(line)
            if m:
                cycles.append((int(m.group(1)), int(m.group(2))))
    events.sort(key=lambda e: e[0])
    disp.sort(key=lambda e: e[0])
    return [(p, c) for _, p, c in events], [t for t, _, _ in events], cycles, disp


def split_runs(seq, start_event):
    runs, cur = [], []
    for ev in seq:
        if ev == start_event and cur:
            runs.append(cur)
            cur = []
        cur.append(ev)
    if cur:
        runs.append(cur)
    return runs


def golden_display_text(golden_file):
    """Program output printed by the IR simulator: text after the final state dump."""
    with open(golden_file, errors="replace") as f:
        content = f.read()
    i = content.rfind("\n  }")
    return None if i < 0 else content[i + 4:].strip("\n")


def golden_display_window(golden_file, proj_dir):
    """(dataStart, printSize): display bytes live at displayLoc + sha(4) + Z(8)."""
    with open(golden_file, errors="replace") as f:
        m = re.search(r"\$display@\[[0-9A-Fa-f]+ \((\d+)\)", f.read())
    if not m:
        return None
    with open(os.path.join(proj_dir, "config.txt")) as f:
        p = re.search(r"printSize = (\d+)", f.read())
    return (int(m.group(1)) + 12, int(p.group(1))) if p else None


def rtl_display_text(disp, window, t_end):
    """Reconstruct the display buffer from write-port traffic of the first run."""
    start, size = window
    buf = {}
    for t, addr, ln, data in disp:
        if t >= t_end:
            break
        for i in range(ln):
            pos = addr + i - start
            if 0 <= pos < size:
                buf[pos] = (data >> (8 * i)) & 0xFF
    out = []
    for pos in range(size):
        if pos not in buf:
            break
        out.append(buf[pos])
    # trailing NULs are startup memory-clear residue, not printed characters
    return bytes(out).rstrip(b"\x00").decode("latin-1").strip("\n")


def first_divergence(a, b):
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i, x, y
    if len(a) != len(b):
        i = min(len(a), len(b))
        return i, (a[i] if i < len(a) else "<end>"), (b[i] if i < len(b) else "<end>")
    return None


def check_project(proj_dir, skip_sim, keep_project):
    name = os.path.basename(proj_dir.rstrip("/"))
    print(f"===== {name}")
    gp = golden_path(proj_dir)
    if not os.path.isfile(gp):
        print(f"  FAIL: golden trace not found: {gp}")
        print("  (run IRSimulatorTest to generate it)")
        return False
    golden = load_golden(gp)
    if not golden:
        print(f"  FAIL: no 'Evaluating ... block' events in {gp}")
        return False

    proj = project_name(proj_dir)
    ensure_fpga_verilog(proj_dir, proj)
    if instrument_tb(proj_dir):
        print("  instrumented fpgaTb.v (original saved as fpgaTb.v.orig)")

    if not skip_sim or not find_simulate_log(proj_dir):
        print("  running Vivado + ModelSim ...")
        run_simulation(proj_dir, keep_project)
    sim_log = find_simulate_log(proj_dir)
    if not sim_log:
        print("  FAIL: no simulate.log produced (see vivado_simcheck.log)")
        return False

    seq, times, cycles, disp = load_rtl(sim_log, real_block_map(proj_dir))
    runs = split_runs(seq, golden[0])
    print(f"  golden events: {len(golden)}; rtl events: {len(seq)} in {len(runs)} run(s); "
          f"exec cycles: {', '.join(f'{c} (exit={s})' for c, s in cycles) or 'n/a'}")
    if not runs:
        print("  FAIL: RTL never executed the entry block "
              f"({golden[0][0]} .{golden[0][1]}) — design did not start or hung")
        return False

    ok = True
    for i, run in enumerate(runs, 1):
        d = first_divergence(run, golden)
        if d is None:
            print(f"  run{i}: MATCH ({len(run)} events)")
        else:
            j, x, y = d
            tag = "FAIL" if i == 1 else "note"
            if i == 1:
                ok = False
            print(f"  run{i}: {tag} — first divergence at event {j}: rtl={x} golden={y}")
            lo = max(0, j - 3)
            print(f"    rtl    context: {run[lo:j+3]}")
            print(f"    golden context: {golden[lo:j+3]}")

    if is_bram_native(proj_dir):
        expected = golden_display_text(gp)
        window = golden_display_window(gp, proj_dir)
        if expected is None or window is None:
            print("  display: SKIP (could not derive expected text/window from golden)")
        else:
            starts = [j for j, ev in enumerate(seq) if ev == golden[0]]
            # cut at the LAST event of run 1: run 2's startup memory-clear loop
            # runs before its $test entry and would wipe the display bytes
            t_end = times[starts[1] - 1] + 1 if len(starts) > 1 else float("inf")
            actual = rtl_display_text(disp, window, t_end)
            if actual == expected:
                print(f"  display: MATCH ({expected!r})")
            else:
                ok = False
                print(f"  display: FAIL — rtl={actual!r} golden={expected!r}")

    print(f"  RESULT: {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("projects", nargs="*", help="project dirs under jvm/result")
    ap.add_argument("--skip-sim", action="store_true",
                    help="reuse existing simulate.log instead of re-simulating")
    ap.add_argument("--keep-project", action="store_true",
                    help="do not delete vivado_project before running")
    args = ap.parse_args()

    projects = args.projects or sorted(
        d for d in glob.glob(os.path.join(RESULT, "*")) if os.path.isdir(d))
    if not projects:
        print(f"no projects found under {RESULT}")
        return 2

    failed = []
    for p in projects:
        p = os.path.abspath(p)
        try:
            if not check_project(p, args.skip_sim, args.keep_project):
                failed.append(os.path.basename(p))
        except Exception as e:
            print(f"  FAIL: {e}")
            failed.append(os.path.basename(p))

    print("=" * 60)
    print(f"{len(projects) - len(failed)}/{len(projects)} projects PASS")
    if failed:
        print("failed:")
        for f in failed:
            print(f"  {f}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
