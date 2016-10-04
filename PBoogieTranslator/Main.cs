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
            var options = new CommandLineArguments(args);
            FSharpExpGen fsExpGen = new FSharpExpGen(options);
            if(options.list)
            {
                using (var sr = new StreamReader(options.inputFile))
                {
                    string line = null;
                    while((line = sr.ReadLine()) != null)
                    {
                        if (line.StartsWith("//"))
                            continue;
                        Console.WriteLine("*************************************************************************************************************************");
                        Console.WriteLine(line);
                        Console.WriteLine("*************************************************************************************************************************");
                        options.pFile = line;
                        Process(options, fsExpGen);
                    }
                    Console.WriteLine("*************************************************************************************************************************");
                }
            }
            else
            {
                options.pFile = options.inputFile;
                Process(options, fsExpGen);
            }
        }

        public static void Process(CommandLineArguments options, FSharpExpGen fsExpGen)
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
            Console.WriteLine("Type checking...");
            ProgramTyping.typecheckProgram(prog);

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
            Console.WriteLine(fileName);
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