using CheckP;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.PBoogieTranslator;
using Microsoft.P2Boogie;
using System.CodeDom.Compiler;
using System.Diagnostics;

namespace Microsoft.TestTranslator
{
    class Tester
    {
        private bool testDesugar;
        private bool testRemoveNT;
        private bool testRemoveSE;
        private bool testBoogie;
        private string listFile = Path.GetFullPath("Correct.txt");

        private const string execsToRun = "/runAll";
        private string[] execDirs = new string[] { "Pc", "Zing", "Prt" };
        private string activeDir;

        //private string activeDir = Path.Combine("..", "P", "Tst");
        private string testDir = Path.Combine("..", "P", "Tst");
        private const string testConfFile = "testconfig.txt";
        private const string goodOutputFile = "goodOutput.txt";
        private PciProcess pciProcess = null;
        private FSharpExpGen fsExpGen = new FSharpExpGen();
        //private Checker pChecker = new Checker();
        private string corralPath = Path.Combine("..", "corral", "bin", "Debug", "corral.exe");

        public Tester(bool testDs, bool testRNT, bool testRSE, bool testBpl, string lsf)
        {
            testDesugar = testDs;
            testRemoveNT = testRNT;
            testRemoveSE = testRSE;
            testBoogie = testBpl;
            if (lsf != null)
            {
                listFile = lsf;
            }

            if (!File.Exists(listFile))
            {
                throw new FileNotFoundException(listFile + " not found!");
            }

            if (testDesugar || testRemoveNT || testRemoveSE)
            {
                string pciPath = Path.Combine("..", "P", "Bld", "Drops", "Debug", "x86", "Binaries", "Pci.exe");
                if (!File.Exists(pciPath))
                {
                    throw new Exception("Pci not found!");
                }
                pciProcess = new PciProcess(pciPath);
            }

            if (testBoogie && !File.Exists(corralPath))
                throw new Exception("Corral not found!");
        }

        public void runTests()
        {
            int numTests = 0;
            int passed = 0;
            int failed = 0;
            string file;
            using (var fileList = new StreamReader(listFile))
            {
                while ((file = fileList.ReadLine()) != null)
                {
                    try
                    {
                        var prog = fsExpGen.genFSExpression(file);
                        if(testDesugar)
                        {
                            bool b = CheckP(prog);
                            if(b)
                            {
                                ++passed;
                            }
                            else
                            {
                                ++failed;
                            }
                            ++numTests;
                        }

                        ProgramTyping.typecheckProgram(prog);

                        prog = RemoveNamedTuples.removeNamedTuplesProgram(prog);
                        if(testRemoveNT)
                        {
                            bool b = CheckP(prog);
                            if (b)
                            {
                                ++passed;
                            }
                            else
                            {
                                ++failed;
                            }
                            ++numTests;
                        }

                        prog = RemoveSideEffects.removeSideEffectsProgram(prog);
                        if(testRemoveSE)
                        {
                            bool b = CheckP(prog);
                            if (b)
                            {
                                ++passed;
                            }
                            else
                            {
                                ++failed;
                            }
                            ++numTests;
                        }
                        if (testBoogie)
                        {
                            bool b = CheckBoogie(file, prog);
                            if (b)
                            {
                                ++passed;
                            }
                            else
                            {
                                ++failed;
                            }
                            ++numTests;
                        }
                    }
                    catch(Exception e)
                    {
                        Console.WriteLine(e.ToString());
                        ++failed;
                    }
                }
            }
        }

        private bool CheckBoogie(string file, Syntax.ProgramDecl prog)
        {
            var pPath = Path.Combine("..", "P", "Tst", "RegressionTests");
            var localFile = file.Replace(@"..\P\Tst", "");
            localFile = Path.ChangeExtension(".p", ".bpl");
            using (var sw = new StreamWriter(localFile))
            {
                using (var itw = new IndentedTextWriter(sw, "    "))
                {
                    Translator.translateProg(prog, itw);
                }
            }
            using (Process corralProcess = new Process())
            {
                var argFilePath = Path.Combine(Path.GetDirectoryName(localFile), testConfFile);
                var goodOutputFilePath = Path.Combine(Path.GetDirectoryName(localFile), goodOutputFile);
                string args = File.ReadAllText(argFilePath);
                ProcessStartInfo info = new ProcessStartInfo(corralPath, args);
                info.RedirectStandardInput = true;
                info.RedirectStandardOutput = true;
                info.UseShellExecute = false;
                corralProcess.StartInfo = info;
                corralProcess.Start();

                var output = corralProcess.StandardOutput.ReadToEnd().Split();
                string goodOutput = File.ReadAllText(goodOutputFilePath);
                
            }

            return false;
        }


        private bool CheckP(Syntax.ProgramDecl prog)
        {
            return false;
        }
    }
}
