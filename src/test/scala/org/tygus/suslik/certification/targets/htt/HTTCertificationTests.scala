package org.tygus.suslik.certification.targets.htt

import java.io.File
import java.nio.file.{Files, Paths}

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.{SynConfig, SynthesisRunnerUtil, defaultConfig}

import scala.sys.process._

/**
  * @author Yasunari Watanabe
  */

class HTTCertificationTests extends FunSpec with Matchers with SynthesisRunnerUtil {
  // Create a temporary directory to store the generated certificates
  // (The directory and its contents remain accessible after the test ends, but are eventually deleted)
  val certRoot: File = Files.createTempDirectory("suslik-").toFile

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(s"certifies that it $desc") {
      synthesizeFromSpec(testName, in, out, params.copy(assertSuccess = false, certTarget = HTT(), certDest = certRoot))
      val fname = testName.split('/').last

      // Find the path to the certificated that was written out to the temp directory
      val fileName = s"${fname.replace('-', '_')}.v"
      val pathToCertificate = Paths.get(certRoot.getCanonicalPath, fileName).toFile.getCanonicalPath

      // Try compiling the ".v" file with coqc
      val result = s"coqc -vok -w none $pathToCertificate".!

      // Check that Coq compilation succeeded with exit code 0
      assert(result == 0)
    }

  describe("SL-based synthesizer with certification") {
    runAllTestsFromDir("certification/ints")
    runAllTestsFromDir("certification/list")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/sll")
    runAllTestsFromDir("certification/dll")
    runAllTestsFromDir("certification/bst")
  }

}