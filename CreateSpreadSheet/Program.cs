using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Office.Interop.Excel;

namespace CreateSpreadSheet
{
    class Program
    {
        static void Main(string[] args)
        {
            var xlApp = new Application();
            if (xlApp == null)
            {
                Console.WriteLine("Excel is not properly installed!");
                return;
            }

            xlApp.Workbooks.Open(@"..\..\..\status.xlsx", 0, false, 5, "", "", true, XlPlatform.xlWindows, "\t", true, false, 0, true, 1, 0);


        }
    }
}
