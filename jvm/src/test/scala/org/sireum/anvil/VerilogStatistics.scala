package org.sireum.anvil

import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.io.Source
import java.io.PrintWriter
import scala.collection.mutable.ArrayBuffer

object VerilogStatistics {

  val currentPath = Paths.get(getClass.getProtectionDomain.getCodeSource.getLocation.toURI)
  val currentDir = if (currentPath.toFile.isFile) currentPath.getParent else currentPath
  val sireumDir = currentDir.getParent.getParent.getParent
  val resultDir = s"${sireumDir}/anvil/jvm/result"

  def countLinesInFile(path: Path): Int = {
    val source = Source.fromFile(path.toFile)
    try {
      source.getLines().size
    } finally {
      source.close()
    }
  }

  def countLinesInFolder(basePath: String, folderName: String, fileExt: String): Int = {
    val targetDir = Paths.get(basePath, folderName)

    if (!Files.exists(targetDir) || !Files.isDirectory(targetDir)) {
      println(s"file not exists: $targetDir")
      return 0
    }

    val files = Files.walk(targetDir).iterator().asScala
      .filter(path => Files.isRegularFile(path) && path.toString.endsWith(fileExt))
      .toList

    val totalLines = files.map(countLinesInFile).sum

    totalLines
  }

  def getSubfolderNames(dirPath: String): Array[String] = {
    val dir = Paths.get(dirPath)
    if (Files.exists(dir) && Files.isDirectory(dir)) {
      val stream = Files.list(dir)
      try {
        stream
          .filter(Files.isDirectory(_))
          .map(_.getFileName.toString)
          .toArray[String](Array.ofDim[String](_))
      } finally {
        stream.close()
      }
    } else {
      Array.empty[String]
    }
  }

  def countLinesAndWriteCSV(fileName: String): Unit = {
    val hashMap = mutable.HashMap[String, mutable.HashMap[String, Int]]()
    val subFolders = getSubfolderNames(resultDir).sorted
    val benchmarks = ArrayBuffer[String]()
    for(i <- 0 until subFolders.length) {
      val parts = subFolders(i).split("_", 2)

      if(!benchmarks.contains(parts(0))) {
        benchmarks += parts(0)
      }

      if(!hashMap.contains(parts(1))) {
        hashMap += (parts(1) ->
          mutable.HashMap[String, Int](parts(0) -> countLinesInFolder(s"${resultDir}/${subFolders(i)}/chisel", "generated_verilog", ".v")))
      } else {
        val subHashMap = hashMap.get(parts(1)).get
        subHashMap += (parts(0) -> countLinesInFolder(s"${resultDir}/${subFolders(i)}/chisel", "generated_verilog", ".v"))
        hashMap(parts(1)) = subHashMap
      }
    }

    var firstRow = "benchmark"
    val arrayKey = ArrayBuffer[String]()
    for(key <- hashMap.keys) {
      firstRow += s",${key.replace(',', '&').replace('_', '&')}"
      arrayKey += key
    }

    val writer = new PrintWriter(s"${resultDir}/${fileName}")
    writer.println(firstRow)
    try {

      for(i <- 0 until benchmarks.length) {
        var benchStr = s"${benchmarks(i)}"
        for(j <- 0 until arrayKey.length) {
          val subHashMap = hashMap.get(arrayKey(j)).get
          benchStr += s",${subHashMap.get(benchmarks(i)).get}"
        }
        writer.println(benchStr)
      }

    } finally {
      writer.close()
    }

  }

  def main(args: Array[String]): Unit = {

    countLinesAndWriteCSV("test.csv")

  }
}
