using Microsoft.PBoogieTranslator;
using System;
using System.IO;

namespace Microsoft.TestTranslator
{
    class Program
    {
        static void Main(string[] args)
        {
            bool testBoogie = true;
            bool testDesugar = false;
            bool testRemoveNT = false;
            bool testRemoveSE = false;
            string listFile = null;

            if (args.Length == 0)
            {
                Console.WriteLine("No flags provided. Running only Boogie Tests.");
            }
            else if (args.Length == 1 && !args[0].StartsWith("/"))
            {
                Console.WriteLine("No flags provided. Running only Boogie Tests.");
                listFile = Path.GetFullPath(args[0]);
            }
            else
            {
                for (int i = 0; i < args.Length; i++)
                {
                    string arg = args[i];
                    if (arg[0] == '-' || arg[0] == '/')
                    {
                        switch (arg.Substring(1).ToLowerInvariant())
                        {
                            case "testDesugar":
                                testDesugar = true;
                                break;
                            case "testRemoveNT":
                                testRemoveNT = true;
                                break;
                            case "testRemoveSE":
                                testRemoveSE = true;
                                break;
                            case "noTestBoogie":
                                testBoogie = false;
                                break;
                            default:
                                goto error;
                        }
                    }
                    else
                    {
                        listFile = Path.GetFullPath(arg);
                    }
                }
            }

            Tester tester = new Tester(testDesugar, testRemoveNT, testRemoveSE, testBoogie, listFile);
            //tester.runTests(); //TODO COME BACK
            return;

            error:
            {
                Console.WriteLine("Usage: Tester.exe [listFile] [options]");
                Console.WriteLine("OPTIONS:");
                Console.WriteLine("/testDesugar");
                Console.WriteLine("/testRemoveNT");
                Console.WriteLine("/testRemoveSE");
                Console.WriteLine("/noTestBoogie");
            }
        }

        private static void runTests()
        {
            throw new NotImplementedException();
        }
    }
}