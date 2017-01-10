using Microsoft.P2Boogie;
using System;
using System.CodeDom.Compiler;
using System.IO;

namespace PBoogieTranslator
{
    internal class CommandLineArguments
    {
        public bool desugar = false;
        public bool removeNT = false;
        public bool removeSE = false;
        public bool genBoogie = true;
        public bool serialize = false;
        public bool test = false;
        public bool genTestOutputs = false;
        public string deSugarFile { get { return Path.Combine(Path.GetDirectoryName(pFile), "deSugared_" + Path.GetFileName(pFile)); } }
        public string removeNTFile { get { return Path.Combine(Path.GetDirectoryName(pFile), "NTRemoved_" + Path.GetFileName(pFile)); } }
        public string removeSEFile { get { return Path.Combine(Path.GetDirectoryName(pFile), "SERemoved_" + Path.GetFileName(pFile)); } }
        public string boogieFile { get { return Path.ChangeExtension(pFile, ".bpl"); } }
    
        public string inputFile = null;
        public string pFile = null;
        public bool list = false;
        public Microsoft.Pc.CommandLineOptions options = new Microsoft.Pc.CommandLineOptions();

        public CommandLineArguments(string[] args)
        {
            options.analyzeOnly = true;
            options.test = true;
            if (args.Length == 0)
            {
                goto error;
            }

            for (int i = 0; i < args.Length; i++)
            {
                string arg = args[i];
                if (arg[0] == '-' || arg[0] == '/')
                {
                    if (inputFile == null)
                    {
                        goto error;
                    }
                    switch (arg.Substring(1).ToLowerInvariant())
                    {
                        case "desugar":
                            desugar = true;
                            break;

                        case "removent":
                            removeNT = true;
                            break;
                        case "removese":
                            removeSE = true;
                            break;
                        case "serialize":
                            serialize = true;
                            break;
                        case "profile":
                            options.profile = true;
                            break;
                        case "list":
                            list = true;
                            break;
                        case "noboogie":
                            genBoogie = false;
                            break;
                        case "test":
                            list = true;
                            test = true;
                            break;
                        case "gentestoutputs":
                            genTestOutputs = true;
                            list = true;
                            break;
                        default:
                            Console.WriteLine("Invalid Option: {0}", arg);
                            goto error;
                    }
                }
                else
                {
                    if (inputFile == null && arg != "testAll")
                    {
                        inputFile = Path.GetFullPath(arg);
                    }
                    else if(arg == "testAll")
                    {
                        inputFile = Path.Combine("..", "..", "..", "Tst", "listOfTests.txt");
                        list = true;
                        test = true;
                    }
                    else
                    {
                        goto error;
                    }
                }
            }
            if (inputFile != null && inputFile.Length > 2)
            {
                if (inputFile.EndsWith(".p"))
                    pFile = inputFile;
                return;
            }
            else if(!inputFile.EndsWith(".txt"))
            {
                Console.WriteLine("Illegal input file name: {0}", inputFile);
            }
        error:
            {
                Console.WriteLine("USAGE: PBoogieTranslator.exe file.p [options]");
                Console.WriteLine("\t/deSugar");
                Console.WriteLine("\t/removeNT");
                Console.WriteLine("\t/removeSE");
                Console.WriteLine("\t/serialize");
                Console.WriteLine("\t/noBoogie");
                Console.WriteLine("We will save to file with names like");
                Console.WriteLine("deSugared_file.p, NTRemoved_file.p, etc.");
                Console.WriteLine("Other options:");
                Console.WriteLine("\t/list");
                Console.WriteLine("\t\tThis option will consider the lines of the input file as file paths.");
                Console.WriteLine("\t/test");
                Console.WriteLine("\t\tThis option will consider the lines of the input file as file paths, and run corral on each output.");
                Console.WriteLine("\t/  genTestOutputs");
                Console.WriteLine("\t\tThis option will consider the lines of the input file as file paths,");
                Console.WriteLine("\t\tand record corral outputs in a format similar to the Regression Tests.");
                Console.WriteLine("\ttestAll");
                Console.WriteLine("\t\tThis option will run all Regression Tests.");
                Environment.Exit(-1);
            }
        }
    }
}