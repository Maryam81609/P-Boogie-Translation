using Microsoft.P2Boogie;
using System;
using System.CodeDom.Compiler;
using System.IO;

namespace PBoogieTranslator
{
    public sealed class CommandLineArguments
    {
        public string deSugarFile = null;
        public string removeNTFile = null;
        public string removeSEFile = null;
        public string boogieFile = null;
        public string inputFile = null;
        public string serializedDSFile = null;
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
                string colonArg = null;
                if (arg[0] == '-' || arg[0] == '/')
                {
                    var colonIndex = arg.IndexOf(':');
                    if (colonIndex >= 0)
                    {
                        arg = args[i].Substring(0, colonIndex);
                        colonArg = args[i].Substring(colonIndex + 1);
                    }
                    if (inputFile == null)
                    {
                        goto error;
                    }
                    switch (arg.Substring(1).ToLowerInvariant())
                    {
                        case "desugar":
                            if (colonArg == null)
                            {
                                var folder = Path.GetDirectoryName(inputFile);
                                var file = Path.GetFileName(inputFile);
                                deSugarFile = Path.Combine(folder, "deSugared_" + file);
                            }
                            break;

                        case "removeNT":
                            if (colonArg == null)
                            {
                                var folder = Path.GetDirectoryName(inputFile);
                                var file = Path.GetFileName(inputFile);
                                removeNTFile = Path.Combine(folder, "NTRemoved_" + file);
                            }
                            break;
                        case "removeSE":
                            if (colonArg == null)
                            {
                                var folder = Path.GetDirectoryName(inputFile);
                                var file = Path.GetFileName(inputFile);
                                removeSEFile = Path.Combine(folder, "SERemoved_" + file);
                            }
                            break;

                        case "outputfilename":
                            if (colonArg == null)
                            {
                                Console.WriteLine("Must supply name for output files");
                                goto error;
                            }
                            else if(colonArg != "-")
                            {
                                boogieFile = Path.GetFullPath(colonArg);
                                var folder = Path.GetDirectoryName(boogieFile);
                                if (!Directory.Exists(folder))
                                {
                                    Console.WriteLine("Output directory {0} does not exist", folder);
                                    goto error;
                                }
                            }
                            break;

                        case "serialize":
                            if (colonArg == null)
                            { 
                                serializedDSFile = Path.ChangeExtension(inputFile, ".dat");
                            }
                            else
                            {
                                serializedDSFile = Path.GetFullPath(colonArg);
                            }
                            break;

                        case "profile":
                            options.profile = true;
                            break;

                        case "list":
                            list = true;
                            break;

                        default:
                            goto error;
                    }
                }
                else
                {
                    if (inputFile == null)
                    {
                        inputFile = Path.GetFullPath(arg);
                        Console.WriteLine(inputFile);
                        boogieFile = Path.ChangeExtension(inputFile, ".bpl");
                    }
                    else
                    {
                        goto error;
                    }
                }
            }
            if (inputFile != null && inputFile.Length > 2 && (inputFile.EndsWith(".p") || inputFile.EndsWith(".txt")))
            {
                return;
            }
            else
            {
                Console.WriteLine("Illegal input file name: {0}", inputFile);
            }
        error:
            {
                Console.WriteLine("USAGE: PBoogieTranslator.exe file.p [options]");
                Console.WriteLine("/deSugar:[name]?");
                Console.WriteLine("/outputFileName:[name]?");
                Console.WriteLine("/removeNT:[name]?");
                Console.WriteLine("/removeSE:[name]?");
                Console.WriteLine("/serialize:[name]?");
                Console.WriteLine("If name is not supplied, we will save to file with names like");
                Console.WriteLine("deSugared_file.p, NTRemoved_file.p, etc.");
                Console.WriteLine("If name is \"-\", output is printed to the terminal.");
                Environment.Exit(-1);
            }
        }
    }
}