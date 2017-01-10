using Microsoft.Pc;
using System;
using System.IO;
using System.Collections.Generic;
using Microsoft.P2Boogie;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;
using System.CodeDom.Compiler;
using PBoogieTranslator;
using System.Diagnostics;

namespace Microsoft.PBoogieTranslator
{
    class Program
    {
        private static int correct = 0;
        private static int wrong = 0;
        private static int tested = 0;
        private static List<string> correctCodes = new List<string>();
        private static List<string> wrongCodes = new List<string>();
        private static string opFileDir = null;
        public static void Main(string[] args)
        {
            var options = new CommandLineArguments(args);
            FSharpExpGen fsExpGen = new FSharpExpGen(options);
            if (options.list)
            {
                using (var sr = new StreamReader(options.inputFile))
                {
                    string line = null;
                    while ((line = sr.ReadLine()) != null)
                    {
                        try
                        {
                            if (line.StartsWith("//"))
                                continue;
                            options.pFile = line;
                            Console.WriteLine("*************************************************************************************************************************");
                            Console.WriteLine(options.boogieFile);
                            Console.WriteLine("*************************************************************************************************************************");
                            Console.Error.WriteLine(options.boogieFile);
                            ProcessPFile(options, fsExpGen);
                            opFileDir = Path.Combine(Path.GetDirectoryName(options.boogieFile), "corral");
                            if (!Directory.Exists(opFileDir))
                                Directory.CreateDirectory(opFileDir);
                            if (options.test)
                                test(options);
                            if (options.genTestOutputs)
                                genTestOutputs(options);
                        }
                        catch (Exception e)
                        {
                            for (int i = 0; i < 3; ++i)
                            {
                                System.Console.Beep();
                            }
                            ++wrong;
                            Console.WriteLine(e);
                            Console.WriteLine(e.StackTrace);
                            Console.WriteLine(e.Source);
                        }
                        finally
                        {
                            ++tested;
                        }
                    }
                    Console.WriteLine("*************************************************************************************************************************");
                }
                System.Console.WriteLine("At most {0} correct, at least {1} wrong, {2} in total", correct, wrong, tested);
                using (var sw = new StreamWriter("correct.txt"))
                {
                    foreach(var x in correctCodes)
                        sw.WriteLine(x);
                }
                using (var sw = new StreamWriter("wrong.txt"))
                {
                    foreach (var x in wrongCodes)
                        sw.WriteLine(x);
                }
            }
            else
            {
                options.pFile = options.inputFile;
                ProcessPFile(options, fsExpGen);
            }
        }

        public static Tuple<bool, string, string> verify(CommandLineArguments options)
        {
            var optFilePath = Path.Combine(opFileDir, "options.txt");
            int rb = 0, k = 0;
            string op = null, err = null;
            if (File.Exists(optFilePath))
            {
                using (var tmp = new StreamReader(optFilePath))
                {
                    var s = tmp.ReadLine().Split();
                    foreach (var e in s)
                    {
                        if (e.StartsWith("/recursionBound:"))
                        {
                            rb = int.Parse(e.Substring(16));
                        }
                        else if (e.StartsWith("/k:"))
                        {
                            k = int.Parse(e.Substring(3));
                        }
                    }
                }
            }
            else
                return new Tuple<bool, string, string> (false, "", "");
            ProcessStartInfo startInfo = new ProcessStartInfo();
            startInfo.FileName = @"..\..\..\corral\bin\Debug\corral.exe";
            startInfo.Arguments = options.boogieFile
                + " /cooperative"  //Use Co-operative scheduling
                + " /timeLimit:1000"
                + " /recursionBound:"
                + rb
                + " /k:"
                + k; //Context switch bound.

            startInfo.RedirectStandardError = true;
            startInfo.RedirectStandardInput = true;
            startInfo.RedirectStandardOutput = true;
            startInfo.UseShellExecute = false;
            Console.Write("Running Corral...");
            var flag = true;
            using (Process process = new Process())
            {
                process.StartInfo = startInfo;
                try
                {
                    process.Start();
                    process.PriorityClass = ProcessPriorityClass.High;
                    op = process.StandardOutput.ReadToEnd();
                    err = process.StandardOutput.ReadToEnd();
                }
                catch (Exception e)
                {
                    Console.WriteLine(e.ToString());
                    Console.WriteLine();
                    Console.Error.WriteLine("ERROR IN CORRAL!");
                    if (flag)
                    {
                        wrong++;
                        wrongCodes.Add(options.boogieFile);
                        flag = false;
                    }
                }
                process.WaitForExit();
                if (process.ExitCode != 0)
                {
                    Console.WriteLine();
                    Console.Error.WriteLine("ERROR IN CORRAL!");
                    if (flag)
                    {
                        wrong++;
                        wrongCodes.Add(options.boogieFile);
                        flag = false;
                    }
                }
                if (flag)
                {
                    correct++;
                    correctCodes.Add(options.boogieFile);
                    Console.Error.WriteLine("Correct!");
                }
                else
                {
                    Console.Error.WriteLine("Wrong!");
                }
            }
            return new Tuple<bool, string, string>(flag, op, err);
        }

        public static void recordBadOp(CommandLineArguments options, string op, string err)
        {

            Console.WriteLine("Check the output of corral in the directory corral\\check-output.log.");
            var path = Path.Combine(opFileDir, "check-output.log");
            using (var sw = new StreamWriter(path))
            {
                sw.WriteLine("STDOUT:");
                sw.WriteLine();
                sw.WriteLine();
                sw.WriteLine(op);
                sw.WriteLine();
                sw.WriteLine();
                sw.WriteLine("STDERR:");
                sw.WriteLine();
                sw.WriteLine();
                sw.WriteLine(err);
                sw.WriteLine();
                sw.WriteLine();
            }
            wrong++;
            wrongCodes.Add(options.boogieFile);
            return;
        }

        public static void genTestOutputs(CommandLineArguments options)
        {
            var res = verify(options);
            var good = res.Item1;
            var op = res.Item2;
            var err = res.Item3;

            if (!good)
            {
                recordBadOp(options, op, err);
                return;
            }

            var idx = op.IndexOf("Boogie verification time");
            if (idx == -1 && op.Contains("Error, internal bug:"))
            {
                idx = op.IndexOf("Error, internal bug:");
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine("ERROR IN CORRAL: ");
                Console.Write("\t");
                Console.WriteLine(op.Substring(idx, op.Substring(idx).IndexOf("\n")));
                recordBadOp(options, op, err);
                return;
            }
            else if(idx == -1)
            {
                Console.WriteLine();
                Console.WriteLine();
                Console.WriteLine("ERROR: Cannot interpret Corral Output.");
                recordBadOp(options, op, err);
                return;
            }

            if ((opFileDir.Contains(@"\Correct\") && op.Contains("Program has a potential bug: True bug")) ||
                    (opFileDir.Contains(@"\DynamicError\") && !op.Contains("Program has a potential bug: True bug")))
            {
                Console.WriteLine("Output incorrect. Error logged at corral\\check-output.log.");
                recordBadOp(options, op, err);
                return;
            }

            using (var sw = new StreamWriter(Path.Combine(opFileDir, "op.txt")))
            {
                try
                {
                    sw.Write(op.Substring(0, idx));
                }
                catch (System.ArgumentOutOfRangeException e)
                {
                    Console.WriteLine("Cannot interpret Corral Output.");
                    recordBadOp(options, op, err);
                    return;
                }
            }
            using (var sw = new StreamWriter(Path.Combine(opFileDir, "stat.txt")))
            {
                sw.Write(op.Substring(idx));
            }
            using (var erf = new StreamWriter(Path.Combine(opFileDir, "err.txt")))
            {
                erf.WriteLine(err);
            }
        }

        private static bool IsDifferent(string op, string file)
        {
            int i = 0;
            string[] lines = op.Split(new string[] { "\r\n", "\n" }, StringSplitOptions.None);
            try
            {
                using (var sr = new StreamReader(file))
                {
                    while (true)
                    {
                        string line1 = lines[i++];
                        string line2 = sr.ReadLine();
                        if (line1 != line2)
                        {
                            return true;
                        }

                        if (line1 == null && line2 == null)
                        {
                            return false;
                        }
                    }
                }
                
            }
            catch
            {
                return true;
            }
        }

        public static bool test(CommandLineArguments options)
        {
            var res = verify(options);
            var op = res.Item2;
            var err = res.Item3;
            if(!res.Item1)
            {
                recordBadOp(options, op, err);
                return false;
            }
            var opFile = Path.Combine(opFileDir, "op.txt");
            if(IsDifferent(op, opFile))
            {
                Console.WriteLine("Outputs do not match.");
                recordBadOp(options, op, err);
                return false;
            }
            return true;
        }

        public static void ProcessPFile(CommandLineArguments options, FSharpExpGen fsExpGen)
        {
            //Desugar the P Program
            var prog = fsExpGen.genFSExpression(options.pFile);
            if(options.desugar)
            {
                printPFile(options.deSugarFile, prog);
            }
            if (options.serialize)
            {
                Save(prog, Path.Combine(Path.GetDirectoryName(options.deSugarFile), 
                    "serialized_" + Path.ChangeExtension(Path.GetFileName(options.deSugarFile), ".bin")));
            }

            //Type check the program.
            Console.Write("Type checking...");
            ProgramTyping.typecheckProgram(prog);
            Console.WriteLine("done!");
            
            //Remove named tuples in the P Program
            prog = RemoveNamedTuples.removeNamedTuplesProgram(prog);
            if(options.removeNT)
            {
                printPFile(options.removeNTFile, prog);
            }
            if (options.serialize)
            {
                Save(prog, Path.Combine(Path.GetDirectoryName(options.removeNTFile), 
                    "serialized_" + Path.ChangeExtension(Path.GetFileName(options.removeNTFile), ".bin")));
            }

            //Remove side effects in the P Program
            prog = RemoveSideEffects.removeSideEffectsProgram(prog);
            if(options.removeSE)
            {
                printPFile(options.removeSEFile, prog);
            }

            if (options.serialize)
            {
                Save(prog, Path.Combine(Path.GetDirectoryName(options.removeSEFile), 
                    "serialized_" + Path.ChangeExtension(Path.GetFileName(options.removeSEFile), ".bin")));
            }

            //Print the Boogie file.
            if (options.genBoogie)
            {
                using (var sw = new StreamWriter(options.boogieFile))
                using (var tr = new IndentedTextWriter(sw, "    "))
                {
                    Translator.translateProg(prog, tr);
                }
            }
        }
        
        //Serialize the F# data structure.
        static void Save(Syntax.ProgramDecl prog, string fileName)
        {
            Stream stream = null;
            try
            {
                IFormatter formatter = new BinaryFormatter();
                stream = new FileStream(fileName, FileMode.Create, FileAccess.Write, FileShare.None);
                formatter.Serialize(stream, prog);
            }
            catch
            {
                // do nothing, just ignore any possible errors
                Console.WriteLine("Error during Serialization.");
            }
            finally
            {
                if (null != stream)
                    stream.Close();
            }
        }

        private static void printPFile(string fileName, Syntax.ProgramDecl prog)
        {
            if (fileName == "-")
            {
                Helper.printProg(new IndentedTextWriter(Console.Out, "   "), prog);
            }
            else if (fileName != null)
            {
                using (var sw = new StreamWriter(fileName))
                using (var tr = new IndentedTextWriter(sw, "    "))
                {
                    Helper.printProg(tr, prog);
                }
            }
            else
            {
                Console.WriteLine("Error: fileName is null");
                Environment.Exit(-1);
            }
        }
    }
}
