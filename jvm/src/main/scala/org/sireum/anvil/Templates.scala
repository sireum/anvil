// #Sireum

package org.sireum.anvil

import org.sireum._
import org.sireum.anvil.Context._

// String templates for vivado-project-generating tcl scripts and petalinux-project-generating shell scripts
// Technically these belong under HardwareContext with arguments for ToolchainContext and ProjectContext,
// but they are being kept separate pending a good way to organize them (and due to their size).
//
// These scripts are created by:
//   (1) Creating a model/reference Vivado project for the given hardware and versions (and some arbitrary hls ip).
//   (2) Running all steps manually in the GUI to produce all desired artifacts
//   (3) Exporting the TCL script to recreate the project
//   (4) Including the TCL script in this file with the following changes:
//       (a) all project-specific values changes to expressions  reference implementation
//       (a) escape codes
//   todo finish top comment
object Templates {

  @pure def zedboard_vivado_2019_2(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): String = {
    val workspace = ec.projectContext.projectWorkspace
    val context = ec.projectContext
    val template_project_part_number = hc.template_project_part_number
    val template_project_top_function = context.template_project_top_function
    val template_project_bus = hc.template_project_bus
    val template_project_hls_directory = workspace.hls.canon.name
    val template_project_vivado_directory = workspace.hw.canon.name
    val template_project_vivado_project = context.template_project_vivado_project // todo make ws.hw direct?
    val template_project_vivado_design = context.template_project_vivado_design

    return s"""
namespace eval _tcl {
proc get_script_folder {} {
  set script_path [file normalize [info script]]
  set script_folder [file dirname ${"$script_path"}]
  return ${"$script_folder"}
}
}
variable script_folder
set script_folder [_tcl::get_script_folder]

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2019.2
set current_vivado_version [version -short]

if { [string first ${"$scripts_vivado_version"} ${"$current_vivado_version]"} == -1 } {
  puts ""
  catch {common::send_msg_id "BD_TCL-109" "ERROR" "This script was generated using Vivado <${"$scripts_vivado_version>"} and is being run in <${"$current_vivado_version>"} of Vivado. Please run the script in Vivado <${"$scripts_vivado_version>"} then open the design in Vivado <${"$current_vivado_version>."} Upgrade the design by running \\"Tools => Report => Report IP Status...\\", then run write_bd_tcl to create an updated script."}

  return 1
}

################################################################
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source ${s"$template_project_vivado_design"}_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./$template_project_vivado_directory/$template_project_vivado_project.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { ${"$list_projs"} eq "" } {
  create_project $template_project_vivado_project $template_project_vivado_directory -part $template_project_part_number
  set_property BOARD_PART digilentinc.com:zedboard:part0:1.0 [current_project]
}


# CHANGE DESIGN NAME HERE
variable design_name
set design_name $template_project_vivado_design

# If you do not already have an existing IP Integrator design open,
# you can create a design using the following command:
#    create_bd_design ${"$design_name"}

# Creating design if needed
set errMsg ""
set nRet 0

set cur_design [current_bd_design -quiet]
set list_cells [get_bd_cells -quiet]

if { ${"${design_name}"} eq "" } {
  # USE CASES:
  #    1) Design_name not set

  set errMsg "Please set the variable <design_name> to a non-empty value."
  set nRet 1

} elseif { ${"${cur_design}"} ne "" && ${"${list_cells}"} eq "" } {
  # USE CASES:
  #    2): Current design opened AND is empty AND names same.
  #    3): Current design opened AND is empty AND names diff; design_name NOT in project.
  #    4): Current design opened AND is empty AND names diff; design_name exists in project.

  if { ${"$cur_design"} ne ${"$design_name"} } {
     common::send_msg_id "BD_TCL-001" "INFO" "Changing value of <design_name> from <${"$design_name>"} to <${"$cur_design>"} since current design is empty."
     set design_name [get_property NAME ${"$cur_design]"}
  }
  common::send_msg_id "BD_TCL-002" "INFO" "Constructing design in IPI design <${"$cur_design"}>..."

} elseif { ${"${cur_design}"} ne "" && ${"$list_cells"} ne "" && ${"$cur_design"} eq ${"$design_name"} } {
  # USE CASES:
  #    5) Current design opened AND has components AND same names.

  set errMsg "Design <${"$design_name>"} already exists in your project, please set the variable <design_name> to another value."
  set nRet 1
} elseif { [get_files -quiet ${"${design_name}.bd]"} ne "" } {
  # USE CASES:
  #    6) Current opened design, has components, but diff names, design_name exists in project.
  #    7) No opened design, design_name exists in project.

  set errMsg "Design <${"$design_name>"} already exists in your project, please set the variable <design_name> to another value."
  set nRet 2

} else {
  # USE CASES:
  #    8) No opened design, design_name not in project.
  #    9) Current opened design, has components, but diff names, design_name not in project.

  common::send_msg_id "BD_TCL-003" "INFO" "Currently there is no design <${"$design_name>"} in project, so creating one..."

  create_bd_design ${"$design_name"}

  common::send_msg_id "BD_TCL-004" "INFO" "Making design <${"$design_name>"} as current_bd_design."
  current_bd_design ${"$design_name"}

}

common::send_msg_id "BD_TCL-005" "INFO" "Currently the variable <design_name> is equal to \\"${"$design_name"}\\"."

if { ${"$nRet"} != 0 } {
  catch {common::send_msg_id "BD_TCL-114" "ERROR" ${"$errMsg"}}
  return ${"$nRet"}
}

##################################################################
# CUSTOM ADDITION - ADD IP CATALOG
##################################################################
set_property  ip_repo_paths ${"$script_folder"}/$template_project_hls_directory/ [current_project]
update_ip_catalog -rebuild

set bCheckIPsPassed 1
##################################################################
# CHECK IPs
##################################################################
#todo add version number to output (or just drop this?)
set bCheckIPs 1
if { ${"$bCheckIPs"} == 1 } {
  set list_check_ips "\\
xilinx.com:hls:$template_project_top_function:1.0\\
xilinx.com:ip:processing_system7:5.5\\
xilinx.com:ip:proc_sys_reset:5.0\\
"

  set list_ips_missing ""
  common::send_msg_id "BD_TCL-006" "INFO" "Checking if the following IPs exist in the project's IP catalog: ${"$list_check_ips"} ."

  foreach ip_vlnv ${"$list_check_ips"} {
     set ip_obj [get_ipdefs -all ${"$ip_vlnv"}]
     if { ${"$ip_obj"} eq "" } {
        lappend list_ips_missing ${"$ip_vlnv"}
     }
  }

  if { ${"$list_ips_missing"} ne "" } {
     catch {common::send_msg_id "BD_TCL-115" "ERROR" "The following IPs are not found in the IP Catalog:\\n  ${"$list_ips_missing\\n\\nResolution:"} Please add the repository containing the IP(s) to the project." }
     set bCheckIPsPassed 0
  }

}

if { ${"$bCheckIPsPassed"} != 1 } {
 common::send_msg_id "BD_TCL-1003" "WARNING" "Will not continue with creation of design due to the error(s) above."
 return 3
}

##################################################################
# DESIGN PROCs
##################################################################



# Procedure to create entire design; Provide argument to make
# procedure reusable. If parentCell is "", will use root.
proc create_root_design { parentCell } {

 variable script_folder
 variable design_name

 if { ${"$parentCell"} eq "" } {
    set parentCell [get_bd_cells /]
 }

 # Get object for parentCell
 set parentObj [get_bd_cells ${"$parentCell"}]
 if { ${"$parentObj"} == "" } {
    catch {common::send_msg_id "BD_TCL-100" "ERROR" "Unable to find parent cell <${"$parentCell"}>!"}
    return
 }

 # Make sure parentObj is hier blk
 set parentType [get_property TYPE ${"$parentObj"}]
 if { ${"$parentType"} ne "hier" } {
    catch {common::send_msg_id "BD_TCL-101" "ERROR" "Parent <${"$parentObj"}> has TYPE = <${"$parentType"}>. Expected to be <hier>."}
    return
 }

 # Save current instance; Restore later
 set oldCurInst [current_bd_instance .]

 # Set parent object as current
 current_bd_instance ${"$parentObj"}


 # Create interface ports
 set DDR [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:ddrx_rtl:1.0 DDR ]

 set FIXED_IO [ create_bd_intf_port -mode Master -vlnv xilinx.com:display_processing_system7:fixedio_rtl:1.0 FIXED_IO ]


 # Create ports

 # Create instance: ${s"$template_project_top_function"}_0, and set properties
 set ${s"$template_project_top_function"}_0 [ create_bd_cell -type ip -vlnv xilinx.com:hls:$template_project_top_function:1.0 ${s"$template_project_top_function"}_0 ]

 # Create instance: processing_system7_0, and set properties
 set processing_system7_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:processing_system7:5.5 processing_system7_0 ]
 set_property -dict [ list \\
  CONFIG.PCW_ACT_APU_PERIPHERAL_FREQMHZ {666.666687} \\
  CONFIG.PCW_ACT_CAN_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_DCI_PERIPHERAL_FREQMHZ {10.158730} \\
  CONFIG.PCW_ACT_ENET0_PERIPHERAL_FREQMHZ {125.000000} \\
  CONFIG.PCW_ACT_ENET1_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA0_PERIPHERAL_FREQMHZ {100.000000} \\
  CONFIG.PCW_ACT_FPGA1_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA2_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA3_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_PCAP_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_QSPI_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_SDIO_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_ACT_SMC_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_SPI_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_TPIU_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_TTC0_CLK0_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC0_CLK1_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC0_CLK2_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK0_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK1_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK2_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_UART_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_ACT_WDT_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_APU_PERIPHERAL_FREQMHZ {666.666667} \\
  CONFIG.PCW_ARMPLL_CTRL_FBDIV {40} \\
  CONFIG.PCW_CAN_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_CAN_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_CAN_PERIPHERAL_FREQMHZ {100} \\
  CONFIG.PCW_CLK0_FREQ {100000000} \\
  CONFIG.PCW_CLK1_FREQ {10000000} \\
  CONFIG.PCW_CLK2_FREQ {10000000} \\
  CONFIG.PCW_CLK3_FREQ {10000000} \\
  CONFIG.PCW_CPU_CPU_PLL_FREQMHZ {1333.333} \\
  CONFIG.PCW_CPU_PERIPHERAL_DIVISOR0 {2} \\
  CONFIG.PCW_DCI_PERIPHERAL_DIVISOR0 {15} \\
  CONFIG.PCW_DCI_PERIPHERAL_DIVISOR1 {7} \\
  CONFIG.PCW_DDRPLL_CTRL_FBDIV {32} \\
  CONFIG.PCW_DDR_DDR_PLL_FREQMHZ {1066.667} \\
  CONFIG.PCW_DDR_PERIPHERAL_DIVISOR0 {2} \\
  CONFIG.PCW_DDR_RAM_HIGHADDR {0x1FFFFFFF} \\
  CONFIG.PCW_ENET0_ENET0_IO {MIO 16 .. 27} \\
  CONFIG.PCW_ENET0_GRP_MDIO_ENABLE {1} \\
  CONFIG.PCW_ENET0_GRP_MDIO_IO {MIO 52 .. 53} \\
  CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR0 {8} \\
  CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_ENET0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_ENET0_PERIPHERAL_FREQMHZ {1000 Mbps} \\
  CONFIG.PCW_ENET0_RESET_ENABLE {0} \\
  CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_ENET1_RESET_ENABLE {0} \\
  CONFIG.PCW_ENET_RESET_ENABLE {1} \\
  CONFIG.PCW_ENET_RESET_SELECT {Share reset pin} \\
  CONFIG.PCW_EN_EMIO_TTC0 {1} \\
  CONFIG.PCW_EN_ENET0 {1} \\
  CONFIG.PCW_EN_GPIO {1} \\
  CONFIG.PCW_EN_QSPI {1} \\
  CONFIG.PCW_EN_SDIO0 {1} \\
  CONFIG.PCW_EN_TTC0 {1} \\
  CONFIG.PCW_EN_UART1 {1} \\
  CONFIG.PCW_EN_USB0 {1} \\
  CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR1 {2} \\
  CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FPGA0_PERIPHERAL_FREQMHZ {100.000000} \\
  CONFIG.PCW_FPGA1_PERIPHERAL_FREQMHZ {150.000000} \\
  CONFIG.PCW_FPGA2_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_FPGA_FCLK0_ENABLE {1} \\
  CONFIG.PCW_FPGA_FCLK1_ENABLE {0} \\
  CONFIG.PCW_FPGA_FCLK2_ENABLE {0} \\
  CONFIG.PCW_FPGA_FCLK3_ENABLE {0} \\
  CONFIG.PCW_GPIO_MIO_GPIO_ENABLE {1} \\
  CONFIG.PCW_GPIO_MIO_GPIO_IO {MIO} \\
  CONFIG.PCW_I2C0_GRP_INT_ENABLE {0} \\
  CONFIG.PCW_I2C0_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_I2C0_RESET_ENABLE {0} \\
  CONFIG.PCW_I2C1_RESET_ENABLE {0} \\
  CONFIG.PCW_I2C_PERIPHERAL_FREQMHZ {25} \\
  CONFIG.PCW_I2C_RESET_ENABLE {1} \\
  CONFIG.PCW_IOPLL_CTRL_FBDIV {30} \\
  CONFIG.PCW_IO_IO_PLL_FREQMHZ {1000.000} \\
  CONFIG.PCW_IRQ_F2P_INTR {1} \\
  CONFIG.PCW_MIO_0_DIRECTION {inout} \\
  CONFIG.PCW_MIO_0_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_0_PULLUP {disabled} \\
  CONFIG.PCW_MIO_0_SLEW {slow} \\
  CONFIG.PCW_MIO_10_DIRECTION {inout} \\
  CONFIG.PCW_MIO_10_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_10_PULLUP {disabled} \\
  CONFIG.PCW_MIO_10_SLEW {slow} \\
  CONFIG.PCW_MIO_11_DIRECTION {inout} \\
  CONFIG.PCW_MIO_11_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_11_PULLUP {disabled} \\
  CONFIG.PCW_MIO_11_SLEW {slow} \\
  CONFIG.PCW_MIO_12_DIRECTION {inout} \\
  CONFIG.PCW_MIO_12_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_12_PULLUP {disabled} \\
  CONFIG.PCW_MIO_12_SLEW {slow} \\
  CONFIG.PCW_MIO_13_DIRECTION {inout} \\
  CONFIG.PCW_MIO_13_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_13_PULLUP {disabled} \\
  CONFIG.PCW_MIO_13_SLEW {slow} \\
  CONFIG.PCW_MIO_14_DIRECTION {inout} \\
  CONFIG.PCW_MIO_14_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_14_PULLUP {disabled} \\
  CONFIG.PCW_MIO_14_SLEW {slow} \\
  CONFIG.PCW_MIO_15_DIRECTION {inout} \\
  CONFIG.PCW_MIO_15_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_15_PULLUP {disabled} \\
  CONFIG.PCW_MIO_15_SLEW {slow} \\
  CONFIG.PCW_MIO_16_DIRECTION {out} \\
  CONFIG.PCW_MIO_16_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_16_PULLUP {disabled} \\
  CONFIG.PCW_MIO_16_SLEW {fast} \\
  CONFIG.PCW_MIO_17_DIRECTION {out} \\
  CONFIG.PCW_MIO_17_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_17_PULLUP {disabled} \\
  CONFIG.PCW_MIO_17_SLEW {fast} \\
  CONFIG.PCW_MIO_18_DIRECTION {out} \\
  CONFIG.PCW_MIO_18_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_18_PULLUP {disabled} \\
  CONFIG.PCW_MIO_18_SLEW {fast} \\
  CONFIG.PCW_MIO_19_DIRECTION {out} \\
  CONFIG.PCW_MIO_19_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_19_PULLUP {disabled} \\
  CONFIG.PCW_MIO_19_SLEW {fast} \\
  CONFIG.PCW_MIO_1_DIRECTION {out} \\
  CONFIG.PCW_MIO_1_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_1_PULLUP {disabled} \\
  CONFIG.PCW_MIO_1_SLEW {fast} \\
  CONFIG.PCW_MIO_20_DIRECTION {out} \\
  CONFIG.PCW_MIO_20_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_20_PULLUP {disabled} \\
  CONFIG.PCW_MIO_20_SLEW {fast} \\
  CONFIG.PCW_MIO_21_DIRECTION {out} \\
  CONFIG.PCW_MIO_21_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_21_PULLUP {disabled} \\
  CONFIG.PCW_MIO_21_SLEW {fast} \\
  CONFIG.PCW_MIO_22_DIRECTION {in} \\
  CONFIG.PCW_MIO_22_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_22_PULLUP {disabled} \\
  CONFIG.PCW_MIO_22_SLEW {fast} \\
  CONFIG.PCW_MIO_23_DIRECTION {in} \\
  CONFIG.PCW_MIO_23_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_23_PULLUP {disabled} \\
  CONFIG.PCW_MIO_23_SLEW {fast} \\
  CONFIG.PCW_MIO_24_DIRECTION {in} \\
  CONFIG.PCW_MIO_24_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_24_PULLUP {disabled} \\
  CONFIG.PCW_MIO_24_SLEW {fast} \\
  CONFIG.PCW_MIO_25_DIRECTION {in} \\
  CONFIG.PCW_MIO_25_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_25_PULLUP {disabled} \\
  CONFIG.PCW_MIO_25_SLEW {fast} \\
  CONFIG.PCW_MIO_26_DIRECTION {in} \\
  CONFIG.PCW_MIO_26_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_26_PULLUP {disabled} \\
  CONFIG.PCW_MIO_26_SLEW {fast} \\
  CONFIG.PCW_MIO_27_DIRECTION {in} \\
  CONFIG.PCW_MIO_27_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_27_PULLUP {disabled} \\
  CONFIG.PCW_MIO_27_SLEW {fast} \\
  CONFIG.PCW_MIO_28_DIRECTION {inout} \\
  CONFIG.PCW_MIO_28_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_28_PULLUP {disabled} \\
  CONFIG.PCW_MIO_28_SLEW {fast} \\
  CONFIG.PCW_MIO_29_DIRECTION {in} \\
  CONFIG.PCW_MIO_29_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_29_PULLUP {disabled} \\
  CONFIG.PCW_MIO_29_SLEW {fast} \\
  CONFIG.PCW_MIO_2_DIRECTION {inout} \\
  CONFIG.PCW_MIO_2_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_2_PULLUP {disabled} \\
  CONFIG.PCW_MIO_2_SLEW {fast} \\
  CONFIG.PCW_MIO_30_DIRECTION {out} \\
  CONFIG.PCW_MIO_30_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_30_PULLUP {disabled} \\
  CONFIG.PCW_MIO_30_SLEW {fast} \\
  CONFIG.PCW_MIO_31_DIRECTION {in} \\
  CONFIG.PCW_MIO_31_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_31_PULLUP {disabled} \\
  CONFIG.PCW_MIO_31_SLEW {fast} \\
  CONFIG.PCW_MIO_32_DIRECTION {inout} \\
  CONFIG.PCW_MIO_32_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_32_PULLUP {disabled} \\
  CONFIG.PCW_MIO_32_SLEW {fast} \\
  CONFIG.PCW_MIO_33_DIRECTION {inout} \\
  CONFIG.PCW_MIO_33_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_33_PULLUP {disabled} \\
  CONFIG.PCW_MIO_33_SLEW {fast} \\
  CONFIG.PCW_MIO_34_DIRECTION {inout} \\
  CONFIG.PCW_MIO_34_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_34_PULLUP {disabled} \\
  CONFIG.PCW_MIO_34_SLEW {fast} \\
  CONFIG.PCW_MIO_35_DIRECTION {inout} \\
  CONFIG.PCW_MIO_35_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_35_PULLUP {disabled} \\
  CONFIG.PCW_MIO_35_SLEW {fast} \\
  CONFIG.PCW_MIO_36_DIRECTION {in} \\
  CONFIG.PCW_MIO_36_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_36_PULLUP {disabled} \\
  CONFIG.PCW_MIO_36_SLEW {fast} \\
  CONFIG.PCW_MIO_37_DIRECTION {inout} \\
  CONFIG.PCW_MIO_37_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_37_PULLUP {disabled} \\
  CONFIG.PCW_MIO_37_SLEW {fast} \\
  CONFIG.PCW_MIO_38_DIRECTION {inout} \\
  CONFIG.PCW_MIO_38_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_38_PULLUP {disabled} \\
  CONFIG.PCW_MIO_38_SLEW {fast} \\
  CONFIG.PCW_MIO_39_DIRECTION {inout} \\
  CONFIG.PCW_MIO_39_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_39_PULLUP {disabled} \\
  CONFIG.PCW_MIO_39_SLEW {fast} \\
  CONFIG.PCW_MIO_3_DIRECTION {inout} \\
  CONFIG.PCW_MIO_3_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_3_PULLUP {disabled} \\
  CONFIG.PCW_MIO_3_SLEW {fast} \\
  CONFIG.PCW_MIO_40_DIRECTION {inout} \\
  CONFIG.PCW_MIO_40_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_40_PULLUP {disabled} \\
  CONFIG.PCW_MIO_40_SLEW {fast} \\
  CONFIG.PCW_MIO_41_DIRECTION {inout} \\
  CONFIG.PCW_MIO_41_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_41_PULLUP {disabled} \\
  CONFIG.PCW_MIO_41_SLEW {fast} \\
  CONFIG.PCW_MIO_42_DIRECTION {inout} \\
  CONFIG.PCW_MIO_42_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_42_PULLUP {disabled} \\
  CONFIG.PCW_MIO_42_SLEW {fast} \\
  CONFIG.PCW_MIO_43_DIRECTION {inout} \\
  CONFIG.PCW_MIO_43_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_43_PULLUP {disabled} \\
  CONFIG.PCW_MIO_43_SLEW {fast} \\
  CONFIG.PCW_MIO_44_DIRECTION {inout} \\
  CONFIG.PCW_MIO_44_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_44_PULLUP {disabled} \\
  CONFIG.PCW_MIO_44_SLEW {fast} \\
  CONFIG.PCW_MIO_45_DIRECTION {inout} \\
  CONFIG.PCW_MIO_45_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_45_PULLUP {disabled} \\
  CONFIG.PCW_MIO_45_SLEW {fast} \\
  CONFIG.PCW_MIO_46_DIRECTION {in} \\
  CONFIG.PCW_MIO_46_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_46_PULLUP {disabled} \\
  CONFIG.PCW_MIO_46_SLEW {slow} \\
  CONFIG.PCW_MIO_47_DIRECTION {in} \\
  CONFIG.PCW_MIO_47_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_47_PULLUP {disabled} \\
  CONFIG.PCW_MIO_47_SLEW {slow} \\
  CONFIG.PCW_MIO_48_DIRECTION {out} \\
  CONFIG.PCW_MIO_48_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_48_PULLUP {disabled} \\
  CONFIG.PCW_MIO_48_SLEW {slow} \\
  CONFIG.PCW_MIO_49_DIRECTION {in} \\
  CONFIG.PCW_MIO_49_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_49_PULLUP {disabled} \\
  CONFIG.PCW_MIO_49_SLEW {slow} \\
  CONFIG.PCW_MIO_4_DIRECTION {inout} \\
  CONFIG.PCW_MIO_4_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_4_PULLUP {disabled} \\
  CONFIG.PCW_MIO_4_SLEW {fast} \\
  CONFIG.PCW_MIO_50_DIRECTION {inout} \\
  CONFIG.PCW_MIO_50_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_50_PULLUP {disabled} \\
  CONFIG.PCW_MIO_50_SLEW {slow} \\
  CONFIG.PCW_MIO_51_DIRECTION {inout} \\
  CONFIG.PCW_MIO_51_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_51_PULLUP {disabled} \\
  CONFIG.PCW_MIO_51_SLEW {slow} \\
  CONFIG.PCW_MIO_52_DIRECTION {out} \\
  CONFIG.PCW_MIO_52_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_52_PULLUP {disabled} \\
  CONFIG.PCW_MIO_52_SLEW {slow} \\
  CONFIG.PCW_MIO_53_DIRECTION {inout} \\
  CONFIG.PCW_MIO_53_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_53_PULLUP {disabled} \\
  CONFIG.PCW_MIO_53_SLEW {slow} \\
  CONFIG.PCW_MIO_5_DIRECTION {inout} \\
  CONFIG.PCW_MIO_5_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_5_PULLUP {disabled} \\
  CONFIG.PCW_MIO_5_SLEW {fast} \\
  CONFIG.PCW_MIO_6_DIRECTION {out} \\
  CONFIG.PCW_MIO_6_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_6_PULLUP {disabled} \\
  CONFIG.PCW_MIO_6_SLEW {fast} \\
  CONFIG.PCW_MIO_7_DIRECTION {out} \\
  CONFIG.PCW_MIO_7_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_7_PULLUP {disabled} \\
  CONFIG.PCW_MIO_7_SLEW {slow} \\
  CONFIG.PCW_MIO_8_DIRECTION {out} \\
  CONFIG.PCW_MIO_8_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_8_PULLUP {disabled} \\
  CONFIG.PCW_MIO_8_SLEW {fast} \\
  CONFIG.PCW_MIO_9_DIRECTION {inout} \\
  CONFIG.PCW_MIO_9_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_9_PULLUP {disabled} \\
  CONFIG.PCW_MIO_9_SLEW {slow} \\
  CONFIG.PCW_MIO_TREE_PERIPHERALS {GPIO#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#UART 1#UART 1#GPIO#GPIO#Enet 0#Enet 0} \\
  CONFIG.PCW_MIO_TREE_SIGNALS {gpio[0]#qspi0_ss_b#qspi0_io[0]#qspi0_io[1]#qspi0_io[2]#qspi0_io[3]/HOLD_B#qspi0_sclk#gpio[7]#gpio[8]#gpio[9]#gpio[10]#gpio[11]#gpio[12]#gpio[13]#gpio[14]#gpio[15]#tx_clk#txd[0]#txd[1]#txd[2]#txd[3]#tx_ctl#rx_clk#rxd[0]#rxd[1]#rxd[2]#rxd[3]#rx_ctl#data[4]#dir#stp#nxt#data[0]#data[1]#data[2]#data[3]#clk#data[5]#data[6]#data[7]#clk#cmd#data[0]#data[1]#data[2]#data[3]#wp#cd#tx#rx#gpio[50]#gpio[51]#mdc#mdio} \\
  CONFIG.PCW_NAND_GRP_D8_ENABLE {0} \\
  CONFIG.PCW_NAND_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_A25_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_CS0_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_CS1_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_CS0_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_CS1_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_INT_ENABLE {0} \\
  CONFIG.PCW_NOR_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_PCAP_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_PJTAG_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_PRESET_BANK0_VOLTAGE {LVCMOS 3.3V} \\
  CONFIG.PCW_PRESET_BANK1_VOLTAGE {LVCMOS 1.8V} \\
  CONFIG.PCW_QSPI_GRP_FBCLK_ENABLE {0} \\
  CONFIG.PCW_QSPI_GRP_IO1_ENABLE {0} \\
  CONFIG.PCW_QSPI_GRP_SINGLE_SS_ENABLE {1} \\
  CONFIG.PCW_QSPI_GRP_SINGLE_SS_IO {MIO 1 .. 6} \\
  CONFIG.PCW_QSPI_GRP_SS1_ENABLE {0} \\
  CONFIG.PCW_QSPI_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_QSPI_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_QSPI_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_QSPI_QSPI_IO {MIO 1 .. 6} \\
  CONFIG.PCW_SD0_GRP_CD_ENABLE {1} \\
  CONFIG.PCW_SD0_GRP_CD_IO {MIO 47} \\
  CONFIG.PCW_SD0_GRP_POW_ENABLE {0} \\
  CONFIG.PCW_SD0_GRP_WP_ENABLE {1} \\
  CONFIG.PCW_SD0_GRP_WP_IO {MIO 46} \\
  CONFIG.PCW_SD0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_SD0_SD0_IO {MIO 40 .. 45} \\
  CONFIG.PCW_SDIO_PERIPHERAL_DIVISOR0 {20} \\
  CONFIG.PCW_SDIO_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_SDIO_PERIPHERAL_VALID {1} \\
  CONFIG.PCW_SINGLE_QSPI_DATA_MODE {x4} \\
  CONFIG.PCW_SMC_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_SPI_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_TPIU_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_TTC0_CLK0_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_CLK1_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_CLK2_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_TTC0_TTC0_IO {EMIO} \\
  CONFIG.PCW_TTC_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_UART1_GRP_FULL_ENABLE {0} \\
  CONFIG.PCW_UART1_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_UART1_UART1_IO {MIO 48 .. 49} \\
  CONFIG.PCW_UART_PERIPHERAL_DIVISOR0 {20} \\
  CONFIG.PCW_UART_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_UART_PERIPHERAL_VALID {1} \\
  CONFIG.PCW_UIPARAM_ACT_DDR_FREQ_MHZ {533.333374} \\
  CONFIG.PCW_UIPARAM_DDR_BANK_ADDR_COUNT {3} \\
  CONFIG.PCW_UIPARAM_DDR_BL {8} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY0 {0.41} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY1 {0.411} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY2 {0.341} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY3 {0.358} \\
  CONFIG.PCW_UIPARAM_DDR_CL {7} \\
  CONFIG.PCW_UIPARAM_DDR_COL_ADDR_COUNT {10} \\
  CONFIG.PCW_UIPARAM_DDR_CWL {6} \\
  CONFIG.PCW_UIPARAM_DDR_DEVICE_CAPACITY {2048 MBits} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_0 {0.025} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_1 {0.028} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_2 {0.001} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_3 {0.001} \\
  CONFIG.PCW_UIPARAM_DDR_DRAM_WIDTH {16 Bits} \\
  CONFIG.PCW_UIPARAM_DDR_FREQ_MHZ {533.333313} \\
  CONFIG.PCW_UIPARAM_DDR_MEMORY_TYPE {DDR 3} \\
  CONFIG.PCW_UIPARAM_DDR_PARTNO {MT41J128M16 HA-15E} \\
  CONFIG.PCW_UIPARAM_DDR_ROW_ADDR_COUNT {14} \\
  CONFIG.PCW_UIPARAM_DDR_SPEED_BIN {DDR3_1066F} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_DATA_EYE {1} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_READ_GATE {1} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_WRITE_LEVEL {1} \\
  CONFIG.PCW_UIPARAM_DDR_T_FAW {45.0} \\
  CONFIG.PCW_UIPARAM_DDR_T_RAS_MIN {36.0} \\
  CONFIG.PCW_UIPARAM_DDR_T_RC {49.5} \\
  CONFIG.PCW_UIPARAM_DDR_T_RCD {7} \\
  CONFIG.PCW_UIPARAM_DDR_T_RP {7} \\
  CONFIG.PCW_UIPARAM_DDR_USE_INTERNAL_VREF {1} \\
  CONFIG.PCW_USB0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_USB0_PERIPHERAL_FREQMHZ {60} \\
  CONFIG.PCW_USB0_RESET_ENABLE {0} \\
  CONFIG.PCW_USB0_USB0_IO {MIO 28 .. 39} \\
  CONFIG.PCW_USB1_RESET_ENABLE {0} \\
  CONFIG.PCW_USB_RESET_ENABLE {1} \\
  CONFIG.PCW_USB_RESET_SELECT {Share reset pin} \\
  CONFIG.PCW_USE_FABRIC_INTERRUPT {1} \\
  CONFIG.preset {ZedBoard} \\
] ${"$processing_system7_0"}

 # Create instance: ps7_0_axi_periph, and set properties
 set ps7_0_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect:2.1 ps7_0_axi_periph ]
 set_property -dict [ list \\
  CONFIG.NUM_MI {2} \\
] ${"$ps7_0_axi_periph"}

 # Create instance: rst_ps7_0_50M, and set properties
 set rst_ps7_0_50M [ create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 rst_ps7_0_50M ]

 # Create interface connections
 connect_bd_intf_net -intf_net processing_system7_0_DDR [get_bd_intf_ports DDR] [get_bd_intf_pins processing_system7_0/DDR]
 connect_bd_intf_net -intf_net processing_system7_0_FIXED_IO [get_bd_intf_ports FIXED_IO] [get_bd_intf_pins processing_system7_0/FIXED_IO]
 connect_bd_intf_net -intf_net processing_system7_0_M_AXI_GP0 [get_bd_intf_pins processing_system7_0/M_AXI_GP0] [get_bd_intf_pins ps7_0_axi_periph/S00_AXI]
 connect_bd_intf_net -intf_net ps7_0_axi_periph_M00_AXI [get_bd_intf_pins ${s"$template_project_top_function"}_0/s_axi_$template_project_bus] [get_bd_intf_pins ps7_0_axi_periph/M00_AXI]

 # Create port connections
 connect_bd_net [get_bd_pins ${s"$template_project_top_function"}_0/interrupt] [get_bd_pins processing_system7_0/IRQ_F2P]
 connect_bd_net -net processing_system7_0_FCLK_CLK0 [get_bd_pins ${s"$template_project_top_function"}_0/ap_clk] [get_bd_pins processing_system7_0/FCLK_CLK0] [get_bd_pins processing_system7_0/M_AXI_GP0_ACLK] [get_bd_pins ps7_0_axi_periph/ACLK] [get_bd_pins ps7_0_axi_periph/M00_ACLK] [get_bd_pins ps7_0_axi_periph/M01_ACLK] [get_bd_pins ps7_0_axi_periph/S00_ACLK] [get_bd_pins rst_ps7_0_50M/slowest_sync_clk]
 connect_bd_net -net processing_system7_0_FCLK_RESET0_N [get_bd_pins processing_system7_0/FCLK_RESET0_N] [get_bd_pins rst_ps7_0_50M/ext_reset_in]
 connect_bd_net -net rst_ps7_0_50M_peripheral_aresetn [get_bd_pins ${s"$template_project_top_function"}_0/ap_rst_n] [get_bd_pins ps7_0_axi_periph/ARESETN] [get_bd_pins ps7_0_axi_periph/M00_ARESETN] [get_bd_pins ps7_0_axi_periph/M01_ARESETN] [get_bd_pins ps7_0_axi_periph/S00_ARESETN] [get_bd_pins rst_ps7_0_50M/peripheral_aresetn]

 # Create address segments
 assign_bd_address -offset 0x43C00000 -range 0x00010000 -target_address_space [get_bd_addr_spaces processing_system7_0/Data] [get_bd_addr_segs ${s"$template_project_top_function"}_0/s_axi_$template_project_bus/Reg] -force


 # Restore current instance
 current_bd_instance ${"$oldCurInst"}

 validate_bd_design
 save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""

# Wrap, Synth, Impl, Gen bitstream

make_wrapper -files [get_files ${"$script_folder"}/$template_project_vivado_directory/$template_project_vivado_project.srcs/sources_1/bd/$template_project_vivado_design/$template_project_vivado_design.bd] -top
add_files -norecurse ${"$script_folder"}/$template_project_vivado_directory/$template_project_vivado_project.srcs/sources_1/bd/$template_project_vivado_design/hdl/${s"$template_project_vivado_design"}_wrapper.v

update_compile_order -fileset sources_1

# (Vivado) Synthesis, Implementation, Bitstream Generation

launch_runs synth_1 -jobs 6
wait_on_run synth_1

launch_runs impl_1 -to_step write_bitstream -jobs 6
wait_on_run impl_1

# Export hardware with bitstream

write_hw_platform -fixed -force -include_bit -file ${"$script_folder"}/$template_project_vivado_directory/${s"$template_project_vivado_design"}_wrapper.xsa
"""
  }

  @pure def zedboard_vivado_2020_1(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): String = {
    val workspace = ec.projectContext.projectWorkspace
    val context = ec.projectContext
    val template_project_part_number = hc.template_project_part_number
    val template_project_top_function = context.template_project_top_function
    val template_project_bus = hc.template_project_bus
    val template_project_hls_directory = workspace.hls.canon.name
    val template_project_vivado_directory = workspace.hw.canon.name
    val template_project_vivado_project = context.template_project_vivado_project // todo make ws.hw direct?
    val template_project_vivado_design = context.template_project_vivado_design

    return s"""
################################################################
# This is a generated script based on design: generatedDesign
#
# Though there are limitations about the generated script,
# the main purpose of this utility is to make learning
# IP Integrator Tcl commands easier.
################################################################

namespace eval _tcl {
proc get_script_folder {} {
  set script_path [file normalize [info script]]
  set script_folder [file dirname ${"$script_path"}]
  return ${"$script_folder"}
}
}
variable script_folder
set script_folder [_tcl::get_script_folder]

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2020.1
set current_vivado_version [version -short]

if { [string first ${"$scripts_vivado_version"} ${"$current_vivado_version]"} == -1 } {
   puts ""
   catch {common::send_gid_msg -ssname BD::TCL -id 2041 -severity "ERROR" "This script was generated using Vivado <${"$scripts_vivado_version"}> and is being run in <${"$current_vivado_version"}> of Vivado. Please run the script in Vivado <${"$scripts_vivado_version"}> then open the design in Vivado <${"$current_vivado_version"}>. Upgrade the design by running \\"Tools => Report => Report IP Status...\\", then run write_bd_tcl to create an updated script."}

   return 1
}

################################################################
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source ${s"$template_project_vivado_design"}_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./$template_project_vivado_directory/$template_project_vivado_project.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { ${"$list_projs"} eq "" } {
   create_project $template_project_vivado_project $template_project_vivado_directory -part $template_project_part_number
   set_property BOARD_PART digilentinc.com:zedboard:part0:1.0 [current_project]
}


# CHANGE DESIGN NAME HERE
variable design_name
set design_name $template_project_vivado_design

# If you do not already have an existing IP Integrator design open,
# you can create a design using the following command:
#    create_bd_design ${"$design_name"}

# Creating design if needed
set errMsg ""
set nRet 0

set cur_design [current_bd_design -quiet]
set list_cells [get_bd_cells -quiet]

if { ${"${design_name}"} eq "" } {
   # USE CASES:
   #    1) Design_name not set

   set errMsg "Please set the variable <design_name> to a non-empty value."
   set nRet 1

} elseif { ${"${cur_design}"} ne "" && ${"${list_cells}"} eq "" } {
   # USE CASES:
   #    2): Current design opened AND is empty AND names same.
   #    3): Current design opened AND is empty AND names diff; design_name NOT in project.
   #    4): Current design opened AND is empty AND names diff; design_name exists in project.

   if { ${"$cur_design"} ne ${"$design_name"} } {
      common::send_gid_msg -ssname BD::TCL -id 2001 -severity "INFO" "Changing value of <design_name> from <${"$design_name"}> to <${"$cur_design"}> since current design is empty."
      set design_name [get_property NAME ${"$cur_design"}]
   }
   common::send_gid_msg -ssname BD::TCL -id 2002 -severity "INFO" "Constructing design in IPI design <${"$cur_design"}>..."

} elseif { ${"${cur_design}"} ne "" && ${"$list_cells"} ne "" && ${"$cur_design"} eq ${"$design_name"} } {
   # USE CASES:
   #    5) Current design opened AND has components AND same names.

   set errMsg "Design <${"$design_name"}> already exists in your project, please set the variable <design_name> to another value."
   set nRet 1
} elseif { ${"[get_files -quiet ${design_name}.bd]"} ne "" } {
   # USE CASES:
   #    6) Current opened design, has components, but diff names, design_name exists in project.
   #    7) No opened design, design_name exists in project.

   set errMsg "Design <${"$design_name"}> already exists in your project, please set the variable <design_name> to another value."
   set nRet 2

} else {
   # USE CASES:
   #    8) No opened design, design_name not in project.
   #    9) Current opened design, has components, but diff names, design_name not in project.

   common::send_gid_msg -ssname BD::TCL -id 2003 -severity "INFO" "Currently there is no design <${"$design_name"}> in project, so creating one..."

   create_bd_design ${"$design_name"}

   common::send_gid_msg -ssname BD::TCL -id 2004 -severity "INFO" "Making design <${"$design_name"}> as current_bd_design."
   current_bd_design ${"$design_name"}

}

common::send_gid_msg -ssname BD::TCL -id 2005 -severity "INFO" "Currently the variable <design_name> is equal to \\"${"$design_name"}\\"."

if { ${"$nRet"} != 0 } {
   catch {common::send_gid_msg -ssname BD::TCL -id 2006 -severity "ERROR" ${"$errMsg"}}
   return ${"$nRet"}
}

##################################################################
# CUSTOM ADDITION - ADD IP CATALOG
##################################################################
set_property ip_repo_paths ${"$script_folder"}/$template_project_hls_directory/ [current_project]
update_ip_catalog -rebuild

set bCheckIPsPassed 1
##################################################################
# CHECK IPs
##################################################################
set bCheckIPs 1
if { ${"$bCheckIPs"} == 1 } {
   set list_check_ips "\\
xilinx.com:hls:$template_project_top_function:1.0\\
xilinx.com:ip:processing_system7:5.5\\
xilinx.com:ip:proc_sys_reset:5.0\\
"

  set list_ips_missing ""
  common::send_gid_msg -ssname BD::TCL -id 2011 -severity "INFO" "Checking if the following IPs exist in the project's IP catalog: ${"$list_check_ips"} ."

  foreach ip_vlnv ${"$list_check_ips"} {
     set ip_obj [get_ipdefs -all ${"$ip_vlnv"}]
     if { ${"$ip_obj"} eq "" } {
        lappend list_ips_missing ${"$ip_vlnv"}
     }
  }

  if { ${"$list_ips_missing"} ne "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2012 -severity "ERROR" "The following IPs are not found in the IP Catalog:\\n  ${"$list_ips_missing"}\\n\\nResolution: Please add the repository containing the IP(s) to the project." }
     set bCheckIPsPassed 0
  }

}

if { ${"$bCheckIPsPassed"} != 1 } {
  common::send_gid_msg -ssname BD::TCL -id 2023 -severity "WARNING" "Will not continue with creation of design due to the error(s) above."
  return 3
}

##################################################################
# DESIGN PROCs
##################################################################



# Procedure to create entire design; Provide argument to make
# procedure reusable. If parentCell is "", will use root.
proc create_root_design { parentCell } {

 variable script_folder
 variable design_name

 if { ${"$parentCell"} eq "" } {
    set parentCell [get_bd_cells /]
 }

 # Get object for parentCell
 set parentObj [get_bd_cells ${"$parentCell"}]
 if { ${"$parentObj"} == "" } {
    catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <${"$parentCell"}>!"}
    return
 }

 # Make sure parentObj is hier blk
 set parentType [get_property TYPE ${"$parentObj"}]
 if { ${"$parentType"} ne "hier" } {
    catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <${"$parentObj"}> has TYPE = <${"$parentType"}>. Expected to be <hier>."}
    return
 }

 # Save current instance; Restore later
 set oldCurInst [current_bd_instance .]

 # Set parent object as current
 current_bd_instance ${"$parentObj"}


 # Create interface ports
 set DDR [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:ddrx_rtl:1.0 DDR ]

 set FIXED_IO [ create_bd_intf_port -mode Master -vlnv xilinx.com:display_processing_system7:fixedio_rtl:1.0 FIXED_IO ]


 # Create ports

 # Create instance: ${s"$template_project_top_function"}_0, and set properties
 set ${s"$template_project_top_function"}_0 [ create_bd_cell -type ip -vlnv xilinx.com:hls:$template_project_top_function:1.0 ${s"$template_project_top_function"}_0 ]

 # Create instance: processing_system7_0, and set properties
 set processing_system7_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:processing_system7:5.5 processing_system7_0 ]
 set_property -dict [ list \\
  CONFIG.PCW_ACT_APU_PERIPHERAL_FREQMHZ {666.666687} \\
  CONFIG.PCW_ACT_CAN_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_DCI_PERIPHERAL_FREQMHZ {10.158730} \\
  CONFIG.PCW_ACT_ENET0_PERIPHERAL_FREQMHZ {125.000000} \\
  CONFIG.PCW_ACT_ENET1_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA0_PERIPHERAL_FREQMHZ {100.000000} \\
  CONFIG.PCW_ACT_FPGA1_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA2_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_FPGA3_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_PCAP_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_QSPI_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_SDIO_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_ACT_SMC_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_SPI_PERIPHERAL_FREQMHZ {10.000000} \\
  CONFIG.PCW_ACT_TPIU_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_ACT_TTC0_CLK0_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC0_CLK1_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC0_CLK2_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK0_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK1_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_TTC1_CLK2_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_ACT_UART_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_ACT_WDT_PERIPHERAL_FREQMHZ {111.111115} \\
  CONFIG.PCW_APU_PERIPHERAL_FREQMHZ {666.666667} \\
  CONFIG.PCW_ARMPLL_CTRL_FBDIV {40} \\
  CONFIG.PCW_CAN_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_CAN_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_CAN_PERIPHERAL_FREQMHZ {100} \\
  CONFIG.PCW_CLK0_FREQ {100000000} \\
  CONFIG.PCW_CLK1_FREQ {10000000} \\
  CONFIG.PCW_CLK2_FREQ {10000000} \\
  CONFIG.PCW_CLK3_FREQ {10000000} \\
  CONFIG.PCW_CPU_CPU_PLL_FREQMHZ {1333.333} \\
  CONFIG.PCW_CPU_PERIPHERAL_DIVISOR0 {2} \\
  CONFIG.PCW_DCI_PERIPHERAL_DIVISOR0 {15} \\
  CONFIG.PCW_DCI_PERIPHERAL_DIVISOR1 {7} \\
  CONFIG.PCW_DDRPLL_CTRL_FBDIV {32} \\
  CONFIG.PCW_DDR_DDR_PLL_FREQMHZ {1066.667} \\
  CONFIG.PCW_DDR_PERIPHERAL_DIVISOR0 {2} \\
  CONFIG.PCW_DDR_RAM_HIGHADDR {0x1FFFFFFF} \\
  CONFIG.PCW_ENET0_ENET0_IO {MIO 16 .. 27} \\
  CONFIG.PCW_ENET0_GRP_MDIO_ENABLE {1} \\
  CONFIG.PCW_ENET0_GRP_MDIO_IO {MIO 52 .. 53} \\
  CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR0 {8} \\
  CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_ENET0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_ENET0_PERIPHERAL_FREQMHZ {1000 Mbps} \\
  CONFIG.PCW_ENET0_RESET_ENABLE {0} \\
  CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_ENET1_RESET_ENABLE {0} \\
  CONFIG.PCW_ENET_RESET_ENABLE {1} \\
  CONFIG.PCW_ENET_RESET_SELECT {Share reset pin} \\
  CONFIG.PCW_EN_EMIO_TTC0 {1} \\
  CONFIG.PCW_EN_ENET0 {1} \\
  CONFIG.PCW_EN_GPIO {1} \\
  CONFIG.PCW_EN_QSPI {1} \\
  CONFIG.PCW_EN_SDIO0 {1} \\
  CONFIG.PCW_EN_TTC0 {1} \\
  CONFIG.PCW_EN_UART1 {1} \\
  CONFIG.PCW_EN_USB0 {1} \\
  CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR1 {2} \\
  CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR1 {1} \\
  CONFIG.PCW_FPGA0_PERIPHERAL_FREQMHZ {100.000000} \\
  CONFIG.PCW_FPGA1_PERIPHERAL_FREQMHZ {150.000000} \\
  CONFIG.PCW_FPGA2_PERIPHERAL_FREQMHZ {50.000000} \\
  CONFIG.PCW_FPGA_FCLK0_ENABLE {1} \\
  CONFIG.PCW_FPGA_FCLK1_ENABLE {0} \\
  CONFIG.PCW_FPGA_FCLK2_ENABLE {0} \\
  CONFIG.PCW_FPGA_FCLK3_ENABLE {0} \\
  CONFIG.PCW_GPIO_MIO_GPIO_ENABLE {1} \\
  CONFIG.PCW_GPIO_MIO_GPIO_IO {MIO} \\
  CONFIG.PCW_I2C0_GRP_INT_ENABLE {0} \\
  CONFIG.PCW_I2C0_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_I2C0_RESET_ENABLE {0} \\
  CONFIG.PCW_I2C1_RESET_ENABLE {0} \\
  CONFIG.PCW_I2C_PERIPHERAL_FREQMHZ {25} \\
  CONFIG.PCW_I2C_RESET_ENABLE {1} \\
  CONFIG.PCW_IOPLL_CTRL_FBDIV {30} \\
  CONFIG.PCW_IO_IO_PLL_FREQMHZ {1000.000} \\
  CONFIG.PCW_IRQ_F2P_INTR {1} \\
  CONFIG.PCW_MIO_0_DIRECTION {inout} \\
  CONFIG.PCW_MIO_0_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_0_PULLUP {disabled} \\
  CONFIG.PCW_MIO_0_SLEW {slow} \\
  CONFIG.PCW_MIO_10_DIRECTION {inout} \\
  CONFIG.PCW_MIO_10_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_10_PULLUP {disabled} \\
  CONFIG.PCW_MIO_10_SLEW {slow} \\
  CONFIG.PCW_MIO_11_DIRECTION {inout} \\
  CONFIG.PCW_MIO_11_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_11_PULLUP {disabled} \\
  CONFIG.PCW_MIO_11_SLEW {slow} \\
  CONFIG.PCW_MIO_12_DIRECTION {inout} \\
  CONFIG.PCW_MIO_12_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_12_PULLUP {disabled} \\
  CONFIG.PCW_MIO_12_SLEW {slow} \\
  CONFIG.PCW_MIO_13_DIRECTION {inout} \\
  CONFIG.PCW_MIO_13_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_13_PULLUP {disabled} \\
  CONFIG.PCW_MIO_13_SLEW {slow} \\
  CONFIG.PCW_MIO_14_DIRECTION {inout} \\
  CONFIG.PCW_MIO_14_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_14_PULLUP {disabled} \\
  CONFIG.PCW_MIO_14_SLEW {slow} \\
  CONFIG.PCW_MIO_15_DIRECTION {inout} \\
  CONFIG.PCW_MIO_15_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_15_PULLUP {disabled} \\
  CONFIG.PCW_MIO_15_SLEW {slow} \\
  CONFIG.PCW_MIO_16_DIRECTION {out} \\
  CONFIG.PCW_MIO_16_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_16_PULLUP {disabled} \\
  CONFIG.PCW_MIO_16_SLEW {fast} \\
  CONFIG.PCW_MIO_17_DIRECTION {out} \\
  CONFIG.PCW_MIO_17_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_17_PULLUP {disabled} \\
  CONFIG.PCW_MIO_17_SLEW {fast} \\
  CONFIG.PCW_MIO_18_DIRECTION {out} \\
  CONFIG.PCW_MIO_18_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_18_PULLUP {disabled} \\
  CONFIG.PCW_MIO_18_SLEW {fast} \\
  CONFIG.PCW_MIO_19_DIRECTION {out} \\
  CONFIG.PCW_MIO_19_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_19_PULLUP {disabled} \\
  CONFIG.PCW_MIO_19_SLEW {fast} \\
  CONFIG.PCW_MIO_1_DIRECTION {out} \\
  CONFIG.PCW_MIO_1_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_1_PULLUP {disabled} \\
  CONFIG.PCW_MIO_1_SLEW {fast} \\
  CONFIG.PCW_MIO_20_DIRECTION {out} \\
  CONFIG.PCW_MIO_20_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_20_PULLUP {disabled} \\
  CONFIG.PCW_MIO_20_SLEW {fast} \\
  CONFIG.PCW_MIO_21_DIRECTION {out} \\
  CONFIG.PCW_MIO_21_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_21_PULLUP {disabled} \\
  CONFIG.PCW_MIO_21_SLEW {fast} \\
  CONFIG.PCW_MIO_22_DIRECTION {in} \\
  CONFIG.PCW_MIO_22_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_22_PULLUP {disabled} \\
  CONFIG.PCW_MIO_22_SLEW {fast} \\
  CONFIG.PCW_MIO_23_DIRECTION {in} \\
  CONFIG.PCW_MIO_23_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_23_PULLUP {disabled} \\
  CONFIG.PCW_MIO_23_SLEW {fast} \\
  CONFIG.PCW_MIO_24_DIRECTION {in} \\
  CONFIG.PCW_MIO_24_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_24_PULLUP {disabled} \\
  CONFIG.PCW_MIO_24_SLEW {fast} \\
  CONFIG.PCW_MIO_25_DIRECTION {in} \\
  CONFIG.PCW_MIO_25_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_25_PULLUP {disabled} \\
  CONFIG.PCW_MIO_25_SLEW {fast} \\
  CONFIG.PCW_MIO_26_DIRECTION {in} \\
  CONFIG.PCW_MIO_26_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_26_PULLUP {disabled} \\
  CONFIG.PCW_MIO_26_SLEW {fast} \\
  CONFIG.PCW_MIO_27_DIRECTION {in} \\
  CONFIG.PCW_MIO_27_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_27_PULLUP {disabled} \\
  CONFIG.PCW_MIO_27_SLEW {fast} \\
  CONFIG.PCW_MIO_28_DIRECTION {inout} \\
  CONFIG.PCW_MIO_28_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_28_PULLUP {disabled} \\
  CONFIG.PCW_MIO_28_SLEW {fast} \\
  CONFIG.PCW_MIO_29_DIRECTION {in} \\
  CONFIG.PCW_MIO_29_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_29_PULLUP {disabled} \\
  CONFIG.PCW_MIO_29_SLEW {fast} \\
  CONFIG.PCW_MIO_2_DIRECTION {inout} \\
  CONFIG.PCW_MIO_2_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_2_PULLUP {disabled} \\
  CONFIG.PCW_MIO_2_SLEW {fast} \\
  CONFIG.PCW_MIO_30_DIRECTION {out} \\
  CONFIG.PCW_MIO_30_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_30_PULLUP {disabled} \\
  CONFIG.PCW_MIO_30_SLEW {fast} \\
  CONFIG.PCW_MIO_31_DIRECTION {in} \\
  CONFIG.PCW_MIO_31_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_31_PULLUP {disabled} \\
  CONFIG.PCW_MIO_31_SLEW {fast} \\
  CONFIG.PCW_MIO_32_DIRECTION {inout} \\
  CONFIG.PCW_MIO_32_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_32_PULLUP {disabled} \\
  CONFIG.PCW_MIO_32_SLEW {fast} \\
  CONFIG.PCW_MIO_33_DIRECTION {inout} \\
  CONFIG.PCW_MIO_33_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_33_PULLUP {disabled} \\
  CONFIG.PCW_MIO_33_SLEW {fast} \\
  CONFIG.PCW_MIO_34_DIRECTION {inout} \\
  CONFIG.PCW_MIO_34_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_34_PULLUP {disabled} \\
  CONFIG.PCW_MIO_34_SLEW {fast} \\
  CONFIG.PCW_MIO_35_DIRECTION {inout} \\
  CONFIG.PCW_MIO_35_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_35_PULLUP {disabled} \\
  CONFIG.PCW_MIO_35_SLEW {fast} \\
  CONFIG.PCW_MIO_36_DIRECTION {in} \\
  CONFIG.PCW_MIO_36_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_36_PULLUP {disabled} \\
  CONFIG.PCW_MIO_36_SLEW {fast} \\
  CONFIG.PCW_MIO_37_DIRECTION {inout} \\
  CONFIG.PCW_MIO_37_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_37_PULLUP {disabled} \\
  CONFIG.PCW_MIO_37_SLEW {fast} \\
  CONFIG.PCW_MIO_38_DIRECTION {inout} \\
  CONFIG.PCW_MIO_38_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_38_PULLUP {disabled} \\
  CONFIG.PCW_MIO_38_SLEW {fast} \\
  CONFIG.PCW_MIO_39_DIRECTION {inout} \\
  CONFIG.PCW_MIO_39_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_39_PULLUP {disabled} \\
  CONFIG.PCW_MIO_39_SLEW {fast} \\
  CONFIG.PCW_MIO_3_DIRECTION {inout} \\
  CONFIG.PCW_MIO_3_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_3_PULLUP {disabled} \\
  CONFIG.PCW_MIO_3_SLEW {fast} \\
  CONFIG.PCW_MIO_40_DIRECTION {inout} \\
  CONFIG.PCW_MIO_40_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_40_PULLUP {disabled} \\
  CONFIG.PCW_MIO_40_SLEW {fast} \\
  CONFIG.PCW_MIO_41_DIRECTION {inout} \\
  CONFIG.PCW_MIO_41_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_41_PULLUP {disabled} \\
  CONFIG.PCW_MIO_41_SLEW {fast} \\
  CONFIG.PCW_MIO_42_DIRECTION {inout} \\
  CONFIG.PCW_MIO_42_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_42_PULLUP {disabled} \\
  CONFIG.PCW_MIO_42_SLEW {fast} \\
  CONFIG.PCW_MIO_43_DIRECTION {inout} \\
  CONFIG.PCW_MIO_43_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_43_PULLUP {disabled} \\
  CONFIG.PCW_MIO_43_SLEW {fast} \\
  CONFIG.PCW_MIO_44_DIRECTION {inout} \\
  CONFIG.PCW_MIO_44_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_44_PULLUP {disabled} \\
  CONFIG.PCW_MIO_44_SLEW {fast} \\
  CONFIG.PCW_MIO_45_DIRECTION {inout} \\
  CONFIG.PCW_MIO_45_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_45_PULLUP {disabled} \\
  CONFIG.PCW_MIO_45_SLEW {fast} \\
  CONFIG.PCW_MIO_46_DIRECTION {in} \\
  CONFIG.PCW_MIO_46_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_46_PULLUP {disabled} \\
  CONFIG.PCW_MIO_46_SLEW {slow} \\
  CONFIG.PCW_MIO_47_DIRECTION {in} \\
  CONFIG.PCW_MIO_47_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_47_PULLUP {disabled} \\
  CONFIG.PCW_MIO_47_SLEW {slow} \\
  CONFIG.PCW_MIO_48_DIRECTION {out} \\
  CONFIG.PCW_MIO_48_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_48_PULLUP {disabled} \\
  CONFIG.PCW_MIO_48_SLEW {slow} \\
  CONFIG.PCW_MIO_49_DIRECTION {in} \\
  CONFIG.PCW_MIO_49_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_49_PULLUP {disabled} \\
  CONFIG.PCW_MIO_49_SLEW {slow} \\
  CONFIG.PCW_MIO_4_DIRECTION {inout} \\
  CONFIG.PCW_MIO_4_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_4_PULLUP {disabled} \\
  CONFIG.PCW_MIO_4_SLEW {fast} \\
  CONFIG.PCW_MIO_50_DIRECTION {inout} \\
  CONFIG.PCW_MIO_50_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_50_PULLUP {disabled} \\
  CONFIG.PCW_MIO_50_SLEW {slow} \\
  CONFIG.PCW_MIO_51_DIRECTION {inout} \\
  CONFIG.PCW_MIO_51_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_51_PULLUP {disabled} \\
  CONFIG.PCW_MIO_51_SLEW {slow} \\
  CONFIG.PCW_MIO_52_DIRECTION {out} \\
  CONFIG.PCW_MIO_52_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_52_PULLUP {disabled} \\
  CONFIG.PCW_MIO_52_SLEW {slow} \\
  CONFIG.PCW_MIO_53_DIRECTION {inout} \\
  CONFIG.PCW_MIO_53_IOTYPE {LVCMOS 1.8V} \\
  CONFIG.PCW_MIO_53_PULLUP {disabled} \\
  CONFIG.PCW_MIO_53_SLEW {slow} \\
  CONFIG.PCW_MIO_5_DIRECTION {inout} \\
  CONFIG.PCW_MIO_5_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_5_PULLUP {disabled} \\
  CONFIG.PCW_MIO_5_SLEW {fast} \\
  CONFIG.PCW_MIO_6_DIRECTION {out} \\
  CONFIG.PCW_MIO_6_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_6_PULLUP {disabled} \\
  CONFIG.PCW_MIO_6_SLEW {fast} \\
  CONFIG.PCW_MIO_7_DIRECTION {out} \\
  CONFIG.PCW_MIO_7_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_7_PULLUP {disabled} \\
  CONFIG.PCW_MIO_7_SLEW {slow} \\
  CONFIG.PCW_MIO_8_DIRECTION {out} \\
  CONFIG.PCW_MIO_8_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_8_PULLUP {disabled} \\
  CONFIG.PCW_MIO_8_SLEW {fast} \\
  CONFIG.PCW_MIO_9_DIRECTION {inout} \\
  CONFIG.PCW_MIO_9_IOTYPE {LVCMOS 3.3V} \\
  CONFIG.PCW_MIO_9_PULLUP {disabled} \\
  CONFIG.PCW_MIO_9_SLEW {slow} \\
  CONFIG.PCW_MIO_TREE_PERIPHERALS {GPIO#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#Quad SPI Flash#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#GPIO#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#Enet 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#USB 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#SD 0#UART 1#UART 1#GPIO#GPIO#Enet 0#Enet 0} \\
  CONFIG.PCW_MIO_TREE_SIGNALS {gpio[0]#qspi0_ss_b#qspi0_io[0]#qspi0_io[1]#qspi0_io[2]#qspi0_io[3]/HOLD_B#qspi0_sclk#gpio[7]#gpio[8]#gpio[9]#gpio[10]#gpio[11]#gpio[12]#gpio[13]#gpio[14]#gpio[15]#tx_clk#txd[0]#txd[1]#txd[2]#txd[3]#tx_ctl#rx_clk#rxd[0]#rxd[1]#rxd[2]#rxd[3]#rx_ctl#data[4]#dir#stp#nxt#data[0]#data[1]#data[2]#data[3]#clk#data[5]#data[6]#data[7]#clk#cmd#data[0]#data[1]#data[2]#data[3]#wp#cd#tx#rx#gpio[50]#gpio[51]#mdc#mdio} \\
  CONFIG.PCW_NAND_GRP_D8_ENABLE {0} \\
  CONFIG.PCW_NAND_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_A25_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_CS0_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_CS1_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_CS0_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_CS1_ENABLE {0} \\
  CONFIG.PCW_NOR_GRP_SRAM_INT_ENABLE {0} \\
  CONFIG.PCW_NOR_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_PCAP_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_PJTAG_PERIPHERAL_ENABLE {0} \\
  CONFIG.PCW_PRESET_BANK0_VOLTAGE {LVCMOS 3.3V} \\
  CONFIG.PCW_PRESET_BANK1_VOLTAGE {LVCMOS 1.8V} \\
  CONFIG.PCW_QSPI_GRP_FBCLK_ENABLE {0} \\
  CONFIG.PCW_QSPI_GRP_IO1_ENABLE {0} \\
  CONFIG.PCW_QSPI_GRP_SINGLE_SS_ENABLE {1} \\
  CONFIG.PCW_QSPI_GRP_SINGLE_SS_IO {MIO 1 .. 6} \\
  CONFIG.PCW_QSPI_GRP_SS1_ENABLE {0} \\
  CONFIG.PCW_QSPI_PERIPHERAL_DIVISOR0 {5} \\
  CONFIG.PCW_QSPI_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_QSPI_PERIPHERAL_FREQMHZ {200.000000} \\
  CONFIG.PCW_QSPI_QSPI_IO {MIO 1 .. 6} \\
  CONFIG.PCW_SD0_GRP_CD_ENABLE {1} \\
  CONFIG.PCW_SD0_GRP_CD_IO {MIO 47} \\
  CONFIG.PCW_SD0_GRP_POW_ENABLE {0} \\
  CONFIG.PCW_SD0_GRP_WP_ENABLE {1} \\
  CONFIG.PCW_SD0_GRP_WP_IO {MIO 46} \\
  CONFIG.PCW_SD0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_SD0_SD0_IO {MIO 40 .. 45} \\
  CONFIG.PCW_SDIO_PERIPHERAL_DIVISOR0 {20} \\
  CONFIG.PCW_SDIO_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_SDIO_PERIPHERAL_VALID {1} \\
  CONFIG.PCW_SINGLE_QSPI_DATA_MODE {x4} \\
  CONFIG.PCW_SMC_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_SPI_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_TPIU_PERIPHERAL_DIVISOR0 {1} \\
  CONFIG.PCW_TTC0_CLK0_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_CLK1_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_CLK2_PERIPHERAL_FREQMHZ {133.333333} \\
  CONFIG.PCW_TTC0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_TTC0_TTC0_IO {EMIO} \\
  CONFIG.PCW_TTC_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_UART1_GRP_FULL_ENABLE {0} \\
  CONFIG.PCW_UART1_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_UART1_UART1_IO {MIO 48 .. 49} \\
  CONFIG.PCW_UART_PERIPHERAL_DIVISOR0 {20} \\
  CONFIG.PCW_UART_PERIPHERAL_FREQMHZ {50} \\
  CONFIG.PCW_UART_PERIPHERAL_VALID {1} \\
  CONFIG.PCW_UIPARAM_ACT_DDR_FREQ_MHZ {533.333374} \\
  CONFIG.PCW_UIPARAM_DDR_BANK_ADDR_COUNT {3} \\
  CONFIG.PCW_UIPARAM_DDR_BL {8} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY0 {0.41} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY1 {0.411} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY2 {0.341} \\
  CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY3 {0.358} \\
  CONFIG.PCW_UIPARAM_DDR_CL {7} \\
  CONFIG.PCW_UIPARAM_DDR_COL_ADDR_COUNT {10} \\
  CONFIG.PCW_UIPARAM_DDR_CWL {6} \\
  CONFIG.PCW_UIPARAM_DDR_DEVICE_CAPACITY {2048 MBits} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_0 {0.025} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_1 {0.028} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_2 {0.001} \\
  CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_3 {0.001} \\
  CONFIG.PCW_UIPARAM_DDR_DRAM_WIDTH {16 Bits} \\
  CONFIG.PCW_UIPARAM_DDR_FREQ_MHZ {533.333313} \\
  CONFIG.PCW_UIPARAM_DDR_MEMORY_TYPE {DDR 3} \\
  CONFIG.PCW_UIPARAM_DDR_PARTNO {MT41J128M16 HA-15E} \\
  CONFIG.PCW_UIPARAM_DDR_ROW_ADDR_COUNT {14} \\
  CONFIG.PCW_UIPARAM_DDR_SPEED_BIN {DDR3_1066F} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_DATA_EYE {1} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_READ_GATE {1} \\
  CONFIG.PCW_UIPARAM_DDR_TRAIN_WRITE_LEVEL {1} \\
  CONFIG.PCW_UIPARAM_DDR_T_FAW {45.0} \\
  CONFIG.PCW_UIPARAM_DDR_T_RAS_MIN {36.0} \\
  CONFIG.PCW_UIPARAM_DDR_T_RC {49.5} \\
  CONFIG.PCW_UIPARAM_DDR_T_RCD {7} \\
  CONFIG.PCW_UIPARAM_DDR_T_RP {7} \\
  CONFIG.PCW_UIPARAM_DDR_USE_INTERNAL_VREF {1} \\
  CONFIG.PCW_USB0_PERIPHERAL_ENABLE {1} \\
  CONFIG.PCW_USB0_PERIPHERAL_FREQMHZ {60} \\
  CONFIG.PCW_USB0_RESET_ENABLE {0} \\
  CONFIG.PCW_USB0_USB0_IO {MIO 28 .. 39} \\
  CONFIG.PCW_USB1_RESET_ENABLE {0} \\
  CONFIG.PCW_USB_RESET_ENABLE {1} \\
  CONFIG.PCW_USB_RESET_SELECT {Share reset pin} \\
  CONFIG.PCW_USE_FABRIC_INTERRUPT {1} \\
  CONFIG.preset {ZedBoard} \\
] ${"$processing_system7_0"}

 # Create instance: ps7_0_axi_periph, and set properties
 set ps7_0_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect:2.1 ps7_0_axi_periph ]
 set_property -dict [ list \\
  CONFIG.NUM_MI {2} \\
] ${"$ps7_0_axi_periph"}

 # Create instance: rst_ps7_0_50M, and set properties
 set rst_ps7_0_50M [ create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 rst_ps7_0_50M ]

 # Create interface connections
 connect_bd_intf_net -intf_net processing_system7_0_DDR [get_bd_intf_ports DDR] [get_bd_intf_pins processing_system7_0/DDR]
 connect_bd_intf_net -intf_net processing_system7_0_FIXED_IO [get_bd_intf_ports FIXED_IO] [get_bd_intf_pins processing_system7_0/FIXED_IO]
 connect_bd_intf_net -intf_net processing_system7_0_M_AXI_GP0 [get_bd_intf_pins processing_system7_0/M_AXI_GP0] [get_bd_intf_pins ps7_0_axi_periph/S00_AXI]
 connect_bd_intf_net -intf_net ps7_0_axi_periph_M00_AXI [get_bd_intf_pins ${s"$template_project_top_function"}_0/s_axi_$template_project_bus] [get_bd_intf_pins ps7_0_axi_periph/M00_AXI]

 # Create port connections
 connect_bd_net [get_bd_pins ${s"$template_project_top_function"}_0/interrupt] [get_bd_pins processing_system7_0/IRQ_F2P]
 connect_bd_net -net processing_system7_0_FCLK_CLK0 [get_bd_pins ${s"$template_project_top_function"}_0/ap_clk] [get_bd_pins processing_system7_0/FCLK_CLK0] [get_bd_pins processing_system7_0/M_AXI_GP0_ACLK] [get_bd_pins ps7_0_axi_periph/ACLK] [get_bd_pins ps7_0_axi_periph/M00_ACLK] [get_bd_pins ps7_0_axi_periph/M01_ACLK] [get_bd_pins ps7_0_axi_periph/S00_ACLK] [get_bd_pins rst_ps7_0_50M/slowest_sync_clk]
 connect_bd_net -net processing_system7_0_FCLK_RESET0_N [get_bd_pins processing_system7_0/FCLK_RESET0_N] [get_bd_pins rst_ps7_0_50M/ext_reset_in]
 connect_bd_net -net rst_ps7_0_50M_peripheral_aresetn [get_bd_pins ${s"$template_project_top_function"}_0/ap_rst_n] [get_bd_pins ps7_0_axi_periph/ARESETN] [get_bd_pins ps7_0_axi_periph/M00_ARESETN] [get_bd_pins ps7_0_axi_periph/M01_ARESETN] [get_bd_pins ps7_0_axi_periph/S00_ARESETN] [get_bd_pins rst_ps7_0_50M/peripheral_aresetn]

 # Create address segments
 assign_bd_address -offset 0x43C00000 -range 0x00010000 -target_address_space [get_bd_addr_spaces processing_system7_0/Data] [get_bd_addr_segs ${s"$template_project_top_function"}_0/s_axi_$template_project_bus/Reg] -force


# Restore current instance
current_bd_instance ${"$oldCurInst"}

validate_bd_design
save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


# Wrap, Synth, Impl, Gen bitstream

make_wrapper -files [get_files ${"$script_folder"}/$template_project_vivado_directory/$template_project_vivado_project.srcs/sources_1/bd/$template_project_vivado_design/$template_project_vivado_design.bd] -top
add_files -norecurse ${"$script_folder"}/$template_project_vivado_directory/$template_project_vivado_project.srcs/sources_1/bd/$template_project_vivado_design/hdl/${s"$template_project_vivado_design"}_wrapper.v

update_compile_order -fileset sources_1

# (Vivado) Synthesis, Implementation, Bitstream Generation

# num jobs is tricky. some steps have max values which can vary per platform (usually 8). todo add in context
# (todo server config)
launch_runs synth_1 -jobs 8
wait_on_run synth_1

# (todo server config)
launch_runs impl_1 -to_step write_bitstream -jobs 8
wait_on_run impl_1

# Export hardware with bitstream

write_hw_platform -fixed -force -include_bit -file ${"$script_folder"}/$template_project_vivado_directory/${s"$template_project_vivado_design"}_wrapper.xsa

"""
  }

  @pure def zedboard_petalinux_2020_1_createSystemUserDtsi(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): String = {
    val scFile: String = "project-spec/meta-user/recipes-bsp/device-tree/files/system-user.dtsi"
    ops.StringOps(scFile).replaceAllLiterally("\r", "")

    val pc = ec.projectContext

    val tab = """$'\t'""" // tab literal in bash

    // todo currently assuming use of default values which could be looked up in project files instead
    return s"""
${"APP_SC_FILE"}=$scFile
echo '/include/ "system-conf.dtsi"' > ${"$APP_SC_FILE"}
echo '/ {' >> ${"$APP_SC_FILE"}
echo '};' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo '/ {' >> ${"$APP_SC_FILE"}
echo ${tab}'model = "Zynq Zed Development Board";' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'compatible = "xlnx,zynq-zed", "xlnx,zynq-7000";' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'usb_phy0: phy0@e0002000 {' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'compatible = "ulpi-phy";' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'#phy-cells = <0>;' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'reg = <0xe0002000 0x1000>;' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'view-port = <0x0170>;' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'drv-vbus;' >> ${"$APP_SC_FILE"}
echo ${tab}'};' >> ${"$APP_SC_FILE"}
echo '};' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo '&clkc {' >> ${"$APP_SC_FILE"}
echo ${tab}'ps-clk-frequency = <33333333>;' >> ${"$APP_SC_FILE"}
echo '};' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo '/ {' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo ${tab}'chosen {' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'bootargs = "console=ttyPS0,115200 earlyprintk uio_pdrv_genirq.of_id=generic-uio";' >> ${"$APP_SC_FILE"}
echo ${tab}'};' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo ${tab}'amba_pl: amba_pl {' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'${pc.template_project_top_function}_0: ${pc.template_project_top_function}@43c00000 {' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}${tab}'compatible = "generic-uio";' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}${tab}'interrupt-parent = <&intc>;' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}${tab}'interrupts = <0 29 1>;' >> ${"$APP_SC_FILE"}
echo ${tab}${tab}'};' >> ${"$APP_SC_FILE"}
echo ${tab}'};' >> ${"$APP_SC_FILE"}
echo '};' >> ${"$APP_SC_FILE"}
echo '' >> ${"$APP_SC_FILE"}
echo '&usb0 {' >> ${"$APP_SC_FILE"}
echo ${tab}'dr_mode = "host";' >> ${"$APP_SC_FILE"}
echo ${tab}'usb-phy = <&usb_phy0>;' >> ${"$APP_SC_FILE"}
echo '};' >> ${"$APP_SC_FILE"}
"""
  }

}
