using Microsoft.Pc;
using System;
using System.IO;
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
        public static void Main(string[] args)
        {
            var options = new CommandLineArguments(args);
            FSharpExpGen fsExpGen = new FSharpExpGen(options);
            int correct = 0;
            int wrong = 0;
            int tested = 0;
            ProcessStartInfo startInfo = new ProcessStartInfo();
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
                            Console.WriteLine("*************************************************************************************************************************");
                            Console.WriteLine(line);
                            Console.WriteLine("*************************************************************************************************************************");
                            options.pFile = line;
                            ProcessPFile(options, fsExpGen);
                            startInfo.FileName = @"..\..\..\corral\bin\Debug\corral.exe";
                            startInfo.Arguments = options.boogieFile + " /cooperative";
                            startInfo.RedirectStandardError = true;
                            startInfo.RedirectStandardInput = true;
                            startInfo.RedirectStandardOutput = true;
                            startInfo.UseShellExecute = false;
                            Console.Write("Running Corral...");
                            using (Process process = new Process())
                            {
                                var flag = true;
                                process.StartInfo = startInfo;
                                try
                                {
                                    process.Start();
                                    var errFile = Path.ChangeExtension(options.boogieFile, ".err.txt");
                                    var opFile = Path.ChangeExtension(options.boogieFile, ".op.txt");
                                    var op = process.StandardOutput.ReadToEnd();
                                    var err = process.StandardOutput.ReadToEnd();
                                    using (var opt = new StreamWriter(opFile))
                                    {
                                        
                                        opt.WriteLine(op);
                                        if(op.Contains("Program has a potential bug: True bug"))
                                        {
                                            Console.WriteLine();
                                            Console.WriteLine(op);
                                            Console.WriteLine(err);
                                            wrong++;
                                            flag = false;
                                        }
                                    }
                                    
                                    using (var erf = new StreamWriter(errFile))
                                    {
                                        erf.WriteLine(err);
                                    }
                                    
                                }
                                catch(Exception e)
                                {
                                    Console.WriteLine(e.ToString());
                                    Console.WriteLine();
                                    Console.WriteLine("ERROR IN CORRAL!");
                                    if(flag)
                                        wrong++;
                                    flag = false;
                                }
                                process.WaitForExit();
                                if(process.ExitCode != 0)
                                {
                                    Console.WriteLine();
                                    Console.WriteLine("ERROR IN CORRAL!");
                                    if(flag)
                                        wrong++;
                                    flag = false;
                                }
                                if (flag)
                                {
                                    correct++;
                                    Console.WriteLine("done!");
                                }
                            }
                            
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
                System.Console.WriteLine("{0} correct, {1} wrong, {2} in total", correct, wrong, tested);
            }
            else
            {
                options.pFile = options.inputFile;
                ProcessPFile(options, fsExpGen);
            }
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
                Save(prog, "serialized_" + options.deSugarFile);
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
                Save(prog, "serialized_" + options.removeNTFile);
            }

            //Remove side effects in the P Program
            prog = RemoveSideEffects.removeSideEffectsProgram(prog);
            if(options.removeSE)
            {
                printPFile(options.removeSEFile, prog);
            }

            if (options.serialize)
            {
                Save(prog, "serialized_" + options.removeSEFile);
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
            }
            finally
            {
                if (null != stream)
                    stream.Close();
            }
        }

        private static void printPFile(string fileName, Syntax.ProgramDecl prog)
        {
            //Console.WriteLine(fileName);
            if (fileName == "-")
            {
                Helper.printProg(prog, new IndentedTextWriter(Console.Out, "   "));
            }
            else if (fileName != null)
            {
                using (var sw = new StreamWriter(fileName))
                using (var tr = new IndentedTextWriter(sw, "    "))
                {
                    Helper.printProg(prog, tr);
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
