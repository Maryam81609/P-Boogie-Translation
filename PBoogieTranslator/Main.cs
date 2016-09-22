
using Microsoft.Pc;
using System;
using System.IO;
using Microsoft.P2Boogie;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;
using System.CodeDom.Compiler;
using PBoogieTranslator;

namespace Microsoft.PBoogieTranslator
{
    class Program
    {
        public static void Main(string[] args)
        {
            //DEBUG: REMOVE!
            args = new string[] { @"C:\Users\teja5832\P\Tst\RegressionTests\Feature1SMLevelDecls\Correct\bug1\bug1.p" };
            var options = new CommandLineArguments(args);
            FSharpExpGen fsExpGen = new FSharpExpGen(options);
            if(options.list)
            {
                using (var ipFile = new StreamReader(options.inputFile))
                {
                    var line = "";
                    while ((line = ipFile.ReadLine()) != null)
                    {
                        if (line.StartsWith("//"))
                            continue;
                        Console.WriteLine("*****************************************************************************");
                        Console.WriteLine(line);
                        Console.WriteLine("*****************************************************************************");
                        workOnProgram(fsExpGen, options, line);
                    }
                }
            }
            else
            {
                workOnProgram(fsExpGen, options, options.inputFile);
            }
        }

        private static void workOnProgram(FSharpExpGen fsExpGen, CommandLineArguments options, string inputFile)
        { 
            //Desugar the P Program
            var prog = fsExpGen.genFSExpression(inputFile);
            if(options.deSugarFile != null)
            {
                printPFile(options.deSugarFile, prog);
            }

            //Type check the program.
            Console.WriteLine("Type checking...");
            ProgramTyping.typecheckProgram(prog);

            //Remove named tuples in the P Program
            prog = RemoveNamedTuples.removeNamedTuplesProgram(prog);
            Console.WriteLine("Removing Named Tuples...");
            if(options.removeNTFile != null)
            {
                printPFile(options.removeNTFile, prog);
            }
            
            //Remove side effects in the P Program
            prog = RemoveSideEffects.removeSideEffectsProgram(prog);
            Console.WriteLine("Removing Side Effects...");
            if (options.removeSEFile != null)
            {
                printPFile(options.removeSEFile, prog);
            }

            //Print the Boogie file.
            Console.WriteLine("Generating Boogie...");
            if (options.boogieFile == "-")
            {
                Translator.translateProg(prog, new IndentedTextWriter(Console.Out, "    "));
            }
            else
            {
                using (var sw = new StreamWriter(options.boogieFile))
                using (var tr = new IndentedTextWriter(sw, "    "))
                {
                    Translator.translateProg(prog, tr);
                }
            }
            
            if(options.serializedDSFile != null)
            {
                Save(prog, options.serializedDSFile);
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