using Microsoft.Pc;
using Microsoft.Pc.Domains;
using System;
using System.Collections.Generic;

using Microsoft.Formula.API.Generators;
using Microsoft.FSharp.Collections;
using Microsoft.FSharp.Core;
using Microsoft.P2Boogie;
using System.IO;

namespace Microsoft.P_FS_Boogie
{
    sealed class FSharpExpGen
    {
        private List<PProgram> parsedPrograms { get; set; }
        private Compiler compiler;
        private static Random r = new Random();

        //Data structures dealing with functions
        private Dictionary<string, List<Syntax.VarDecl>> 
            functionsToLocals = new Dictionary<string, List<Syntax.VarDecl>>();

        //Data Structures Dealing with States
        private Dictionary<string, List<Syntax.DoDecl.T>>
            statesToDos = new Dictionary<string, List<Syntax.DoDecl.T>>();
        private Dictionary<string, List<Syntax.TransDecl.T>>
            statesToTransitions = new Dictionary<string, List<Syntax.TransDecl.T>>();

        //Data Structures Dealing with machines.
        private Dictionary<string, List<Syntax.StateDecl>> machineToStateList = new Dictionary<string, List<Syntax.StateDecl>>();
        private Dictionary<string, HashSet<Syntax.FunDecl>> machineToFunList = new Dictionary<string, HashSet<Syntax.FunDecl>>();
        private Dictionary<string, List<Syntax.VarDecl>> machineToVars = new Dictionary<string, List<Syntax.VarDecl>>();
        private Dictionary<string, List<string>> monitorToEventList = new Dictionary<string, List<string>>();
        private bool hasPush = false;

        //Data structures dealing with the program itself.
        private List<Syntax.FunDecl> staticFunctions = new List<Syntax.FunDecl>();
        private List<Syntax.MachineDecl> machines = new List<Syntax.MachineDecl>();
        private List<Syntax.EventDecl> events = new List<Syntax.EventDecl>();
        private Dictionary<string, Syntax.Type> 
            typeDefs = new Dictionary<string, Syntax.Type>();
        private Dictionary<string, Syntax.EventDecl> 
            eventsToDecls = new Dictionary<string, Syntax.EventDecl>();
        private Dictionary<string, List<string>> 
            eventToMonitorList = new Dictionary<string, List<string>>();
        private Dictionary<string, List<Tuple<int, string, Syntax.Type>>> 
            functionsToRefParams = new Dictionary<string, List<Tuple<int, string, Syntax.Type>>>();
        private Dictionary<P_Root.AnonFunDecl, string> anonFunToFileName = 
            new Dictionary<P_Root.AnonFunDecl, string>();
        private Dictionary<P_Root.FunDecl, string> FunToFileName =
           new Dictionary<P_Root.FunDecl, string>();

        private string mainMachine = null;
        private SymbolTable symbolTable = new SymbolTable();
        private int maxFields = 0;
        private bool hasDefer = false;
        private bool hasIgnore = false;
        private string fileName = null;

        public FSharpExpGen(CommandLineOptions options)
        {
            options.analyzeOnly = true;
            options.profile = true;
            options.test = true;
            compiler = new Compiler(options);
        }

        private static string getString(ICSharpTerm x)
        {
            try
            {
                return (x as P_Root.StringCnst).Value;
            }
            catch (NullReferenceException e)
            {
                Console.WriteLine("The value passed cannot be converted to a String.");
                Console.WriteLine(x.GetType().ToString());
                Console.WriteLine(e.StackTrace);
                return "";
            }
        }

        private static int getValue(ICSharpTerm x)
        {
            int i;
            Formula.Common.Rational a = (x as P_Root.RealCnst).Value;
            if (a.IsInteger)
            {
                if (int.TryParse(a.ToString(0), out i))
                    return i;
            }
            else
            {
                throw new InvalidOperationException("The value passed cannot be converted to an Integer/Natural.");
            }
            return -1;
        }

        private string getQualifiedName(P_Root.QualifiedName n)
        {
            string ret = "";
            if (n.qualifier.Symbol.ToString() != "NIL")
            {
                ret = getQualifiedName(n.qualifier as P_Root.QualifiedName);
                ret += "_";
            }
            ret += getString(n.name);
            return ret;
        }

        private int getLineNumber(P_Root.Stmt s)
        {
            if (s is P_Root.NewStmt)
            {
                var x = (s as P_Root.NewStmt);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Raise)
            {
                var x = (s as P_Root.Raise);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Send)
            {
                var x = (s as P_Root.Send);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Monitor)
            {
                var x = (s as P_Root.Monitor);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.FunStmt)
            {
                var x = (s as P_Root.FunStmt);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.NulStmt)
            {
                var x = (s as P_Root.NulStmt);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.BinStmt)
            {
                var x = (s as P_Root.BinStmt);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Return)
            {
                var x = (s as P_Root.Return);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.While)
            {
                var x = (s as P_Root.While);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Ite)
            {
                var x = (s as P_Root.Ite);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Seq)
            {
                var x = (s as P_Root.Seq).s1 as P_Root.Stmt;
                return getLineNumber(x);
            }
            else if (s is P_Root.Receive)
            {
                var x = (s as P_Root.Receive);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if (s is P_Root.Assert)
            {
                var x = (s as P_Root.Assert);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            else if(s is P_Root.Print)
            {
                var x = (s as P_Root.Print);
                var l = (x.info as P_Root.SourceInfo).line;
                return getValue(l as P_Root.Natural);
            }
            return -1;
        }

        private void NewScope(string name)
        {
            symbolTable.NewScope(name);
            functionsToLocals[name] = new List<Syntax.VarDecl>();    
            functionsToRefParams[name] = new List<Tuple<int, string, Syntax.Type>>();
        }

        private void ExitScope()
        {
            symbolTable.ExitScope();
        }

        private Syntax.Type genBaseType(P_Root.BaseType t)
        {
            if (t._0.Symbol.ToString() == "INT")
            {
                return Syntax.Type.Int;
            }
            else if (t._0.Symbol.ToString() == "BOOL")
            {
                return Syntax.Type.Bool;
            }
            else if (t._0.Symbol.ToString() == "MACHINE")
            {
                return Syntax.Type.Machine;
            }
            else if (t._0.Symbol.ToString() == "ANY")
            {
                return Syntax.Type.Any;
            }
            else if (t._0.Symbol.ToString() == "EVENT")
            {
                return Syntax.Type.Event;
            }
            else if (t._0.Symbol.ToString() == "NULL")
            {
                return Syntax.Type.Null;
            }
            return null;
        }

        private Syntax.Type.Tuple genTupType(P_Root.TupType t)
        {
            var x = t;
            var lst = new List<Syntax.Type>();
            do
            {
                var z = genTypeExpr(x.hd as P_Root.TypeExpr);
                if (z == null)
                    return null;
                lst.Add(z);
                x = x.tl as P_Root.TupType;
            } while (x != null);
            if (lst.Count > maxFields)
                maxFields = lst.Count;
            return Syntax.Type.NewTuple(ListModule.OfSeq(lst)) as Syntax.Type.Tuple;
        }

        private Tuple<string, Syntax.Type> genNmdTupTypeField(P_Root.NmdTupTypeField f)
        {
            var name = getString(f.name);
            var type = genTypeExpr(f.type as P_Root.TypeExpr);
            if (type == null)
                return null;
            return new Tuple<string, Syntax.Type>(name, type);
        }

        private List<Tuple<string, Syntax.Type>> genNmdTupTypeList(P_Root.NmdTupType t)
        {
            var lst = new List<Tuple<string, Syntax.Type>>();
            var x = t;
            do
            {
                var z = genNmdTupTypeField(x.hd as P_Root.NmdTupTypeField);
                if (z == null)
                    return null;
                lst.Add(z);
                x = x.tl as P_Root.NmdTupType;
            }
            while (x != null);
            return lst;
        }

        private Syntax.Type.NamedTuple genNmdTupType(P_Root.NmdTupType t)
        {
            var lst = genNmdTupTypeList(t);
            if (lst == null)
                return null;
            if (lst.Count > maxFields)
                maxFields = lst.Count;
            return Syntax.Type.NewNamedTuple(ListModule.OfSeq(lst)) 
                as Syntax.Type.NamedTuple;
        }

        private Syntax.Type.Seq genSeqType(P_Root.SeqType t)
        {
            var x = genTypeExpr(t.x as P_Root.TypeExpr);
            if (x == null)
                return null;
            return Syntax.Type.NewSeq(x) as Syntax.Type.Seq;
        }

        private Syntax.Type.Map genMapType(P_Root.MapType t)
        {
            var k = genTypeExpr(t.k as P_Root.TypeExpr);
            var v = genTypeExpr(t.v as P_Root.TypeExpr);
            if (k == null || v == null)
                return null;
            return Syntax.Type.NewMap(k, v) as Syntax.Type.Map;
        }

        private Syntax.Type genNameType(P_Root.NameType t)
        {
            var name = getString(t.name);
            Syntax.Type res;
            if (typeDefs.TryGetValue(name, out res))
                return res;
            else
                return null;
        }

        private Syntax.Type genTypeExpr(P_Root.TypeExpr t)
        {
            //t: any TypeExpr. This means we can check its derived type as we wish.
            if (t is P_Root.NameType)
            {
                return genNameType(t as P_Root.NameType);
            }
            else if (t is P_Root.BaseType)
            {
                return genBaseType(t as P_Root.BaseType);
            }
            else if (t is P_Root.SeqType)
            {
                return genSeqType(t as P_Root.SeqType);
            }
            else if (t is P_Root.TupType)
            {
                return genTupType(t as P_Root.TupType);
            }
            else if (t is P_Root.NmdTupType)
            {
                return genNmdTupType(t as P_Root.NmdTupType);
            }
            else if (t is P_Root.MapType)
            {
                return genMapType(t as P_Root.MapType);
            }
            return null;
        }

        private Syntax.Expr genName(P_Root.Name e)
        {
            var name = getString(e.name);
            var symName = symbolTable.GetVarName(name);
            if (name != symName)
                return Syntax.Expr.NewVar(symName) as Syntax.Expr.Var;
            else if(eventsToDecls.ContainsKey(name))
                return Syntax.Expr.NewEvent(name);
            throw new InvalidProgramException("No such variable/event as " + name);
        }

        private Syntax.Expr.New genNewExpr(P_Root.New e)
        {
            var s = getString(e.name);
            Syntax.Expr x = Syntax.Expr.Nil;
            if (e.arg.Symbol.ToString() != "NIL")
            {
                x = genExpr(e.arg as P_Root.Expr);
            }
            return Syntax.Expr.NewNew(s, x) as Syntax.Expr.New;
        }

        private Syntax.Expr.Call genFunApp(P_Root.FunApp e)
        {
            var n = symbolTable.GetFunName(getString(e.name));
            FSharpList<Syntax.Expr> args = FSharpList<Syntax.Expr>.Empty;
            if (e.args.Symbol.ToString() != "NIL")
            {
                args = genExprs(e.args as P_Root.Exprs);
            }
            return Syntax.Expr.NewCall(n, args) as Syntax.Expr.Call;
        }

        private Syntax.Expr genNulApp(P_Root.NulApp e)
        {
            if (e.op is P_Root.Integer)
            {
                var x = getValue(e.op as P_Root.Integer);
                return Syntax.Expr.NewConstInt(x);
            }
            else
            {
                switch (e.op.Symbol.ToString())
                {
                    case "TRUE":
                        return Syntax.Expr.NewConstBool(true);
                    case "FALSE":
                        return Syntax.Expr.NewConstBool(false);
                    case "THIS":
                        return Syntax.Expr.This;
                    case "FAIRNONDET":
                    case "NONDET":
                        return Syntax.Expr.Nondet;
                    case "NULL":
                        //Syntax.Expr.NewEvent("null") ?
                        return Syntax.Expr.Nil;
                    case "HALT":
                        return Syntax.Expr.NewEvent("halt");
                    default:
                        throw new InvalidOperationException("Error in NulApp Generation: got symbol " + e.op.Symbol.ToString());
                }
            }
        }

        private Syntax.UnOp genUnOp(P_Root.IArgType_UnApp__0 op)
        {
            switch (op.Symbol.ToString())
            {
                case "NOT":
                    return Syntax.UnOp.Not;
                case "NEG":
                    return Syntax.UnOp.Neg;
                case "KEYS":
                    return Syntax.UnOp.Keys;
                case "VALUES":
                    return Syntax.UnOp.Values;
                case "SIZEOF":
                    return Syntax.UnOp.Sizeof;
                default:
                    throw new InvalidOperationException("Error in UnApp Generation: got symbol " + op.Symbol.ToString());
            }

        }

        private Syntax.BinOp genBinOp(P_Root.IArgType_BinApp__0 op)
        {
            switch (op.Symbol.ToString())
            {
                case "ADD":
                    return Syntax.BinOp.Add;
                case "SUB":
                    return Syntax.BinOp.Sub;
                case "MUL":
                    return Syntax.BinOp.Mul;
                case "INTDIV":
                    return Syntax.BinOp.Intdiv;
                case "AND":
                    return Syntax.BinOp.And;
                case "OR":
                    return Syntax.BinOp.Or;
                case "EQ":
                    return Syntax.BinOp.Eq;
                case "NEQ":
                    return Syntax.BinOp.Neq;
                case "LT":
                    return Syntax.BinOp.Lt;
                case "LE":
                    return Syntax.BinOp.Le;
                case "GT":
                    return Syntax.BinOp.Gt;
                case "GE":
                    return Syntax.BinOp.Ge;
                case "IDX":
                    return Syntax.BinOp.Idx;
                case "IN":
                    return Syntax.BinOp.In;
                default:
                    throw new InvalidOperationException("Error in BinApp Generation: got symbol " + op.Symbol.ToString());
            }
        }

        private Syntax.Expr genFieldExpr(P_Root.Field e)
        {
            var arg = genExpr(e.arg as P_Root.Expr);
            if (e.name is P_Root.Natural)
            {
                var f = getValue(e.name as P_Root.Natural);
                return Syntax.Expr.NewDot(arg, f);
            }
            else if (e.name is P_Root.String)
            {
                var f = getString(e.name);
                return Syntax.Expr.NewNamedDot(arg, f);
            }
            return null;
        }

        private Syntax.Expr.Default genDefaultExpr(P_Root.Default e)
        {
            var t = genTypeExpr(e.type as P_Root.TypeExpr);
            return Syntax.Expr.NewDefault(t) as Syntax.Expr.Default;
        }

        private Syntax.Expr.Cast genCastExpr(P_Root.Cast e)
        {
            var arg = genExpr(e.arg as P_Root.Expr);
            var t = genTypeExpr(e.type as P_Root.TypeExpr);
            return Syntax.Expr.NewCast(arg, t) as Syntax.Expr.Cast;
        }

        private FSharpList<Syntax.Expr> genExprs(P_Root.Exprs e)
        {
            var x = e;
            List<Syntax.Expr> lst = new List<Syntax.Expr>();
            do
            {
                lst.Add(genExpr(x.head as P_Root.Expr));
                x = x.tail as P_Root.Exprs;
            }
            while (x != null);
            return ListModule.OfSeq(lst);
        }

        private FSharpList<Tuple<string, Syntax.Expr>> genNamedExprs(P_Root.NamedExprs e)
        {
            var x = e;
            List<Tuple<string, Syntax.Expr>> lst = new List<Tuple<string, Syntax.Expr>>();
            do
            {
                var f = getString(x.field);
                var exp = genExpr(x.exp as P_Root.Expr);
                var t = new Tuple<string, Syntax.Expr>(f, exp);
                lst.Add(t);
                x = x.tail as P_Root.NamedExprs;
            } while (x != null);
            return ListModule.OfSeq(lst);
        }

        private Syntax.Expr.Tuple genTupleExpr(P_Root.Tuple e)
        {
            var x = genExprs(e.body as P_Root.Exprs);
            return Syntax.Expr.NewTuple(x) as Syntax.Expr.Tuple;
        }

        private Syntax.Expr.NamedTuple genNamedTupleExpr(P_Root.NamedTuple e)
        {
            var x = genNamedExprs(e.body as P_Root.NamedExprs);
            return Syntax.Expr.NewNamedTuple(x) as Syntax.Expr.NamedTuple;
        }

        private Syntax.Expr.Un genUnApp(P_Root.UnApp u)
        {
            var op = genUnOp(u.op as P_Root.IArgType_UnApp__0);
            var arg = genExpr(u.arg1 as P_Root.Expr);
            return Syntax.Expr.NewUn(op, arg) as Syntax.Expr.Un;
        }

        private Syntax.Expr.Bin genBinApp(P_Root.BinApp b)
        {
            var op = genBinOp(b.op as P_Root.IArgType_BinApp__0);
            var arg1 = genExpr(b.arg1 as P_Root.Expr);
            var arg2 = genExpr(b.arg2 as P_Root.Expr);
            return Syntax.Expr.NewBin(op, arg1, arg2) as Syntax.Expr.Bin;
        }

        private Syntax.Expr genExpr(P_Root.Expr e)
        {
            if (e is P_Root.Name)
            {
                return genName((e as P_Root.Name));
            }
            else if (e is P_Root.New)
            {
                return genNewExpr((e as P_Root.New));
            }
            else if (e is P_Root.FunApp)
            {
                return genFunApp((e as P_Root.FunApp));
            }
            else if (e is P_Root.NulApp)
            {
                return genNulApp((e as P_Root.NulApp));
            }
            else if (e is P_Root.UnApp)
            {
                return genUnApp((e as P_Root.UnApp));
            }
            else if (e is P_Root.BinApp)
            {
                return genBinApp((e as P_Root.BinApp));
            }
            else if (e is P_Root.Field)
            {
                return genFieldExpr((e as P_Root.Field));
            }
            else if (e is P_Root.Default)
            {
                return genDefaultExpr((e as P_Root.Default));
            }
            else if (e is P_Root.Cast)
            {
                return genCastExpr((e as P_Root.Cast));
            }
            else if (e is P_Root.Tuple)
            {
                return genTupleExpr((e as P_Root.Tuple));
            }
            else if (e is P_Root.NamedTuple)
            {
                return genNamedTupleExpr((e as P_Root.NamedTuple));
            }
            return Syntax.Expr.Nil;
        }

        private Syntax.Stmt.NewStmt genNewStmt(P_Root.NewStmt s)
        {
            var n = getString(s.name);
            Syntax.Expr arg = Syntax.Expr.Nil;
            if (s.arg.Symbol.ToString() != "NIL")
            {
                arg = genExpr(s.arg as P_Root.Expr);
            }
            return Syntax.Stmt.NewNewStmt(n, arg) as Syntax.Stmt.NewStmt;
        }

        private Syntax.Stmt.Raise genRaiseStmt(P_Root.Raise s)
        {
            var ev = genExpr(s.ev as P_Root.Expr);
            var arg = Syntax.Expr.Nil;
            if (s.arg.Symbol.ToString() != "NIL")
            {
                arg = genExpr(s.arg as P_Root.Expr);
            }
            return Syntax.Stmt.NewRaise(ev, arg) as Syntax.Stmt.Raise;
        }

        private Syntax.Stmt.Send genSendStmt(P_Root.Send s)
        {
            var dst = genExpr(s.dest as P_Root.Expr);
            var ev = genExpr(s.ev as P_Root.Expr);
            Syntax.Expr arg = Syntax.Expr.Nil;
            if (s.arg.Symbol.ToString() != "NIL")
            {
                arg = genExpr(s.arg as P_Root.Expr);
            }
            return Syntax.Stmt.NewSend(dst, ev, arg) as Syntax.Stmt.Send;
        }

        private Syntax.Stmt.Monitor genMonitorStmt(P_Root.Monitor s)
        {
            var ev = genExpr(s.ev as P_Root.Expr);
            Syntax.Expr arg = Syntax.Expr.Nil;
            if (s.arg.Symbol.ToString() != "NIL")
            {
                arg = genExpr(s.arg as P_Root.Expr);
            }
            return Syntax.Stmt.NewMonitor(ev, arg) as Syntax.Stmt.Monitor;
        }

        private Syntax.Stmt.FunStmt genFunStmt(P_Root.FunStmt s)
        {
            var n = symbolTable.GetFunName(getString(s.name));
            FSharpList<Syntax.Expr> args = FSharpList<Syntax.Expr>.Empty;
            FSharpOption<string> aout = null;
            if (s.args.Symbol.ToString() != "NIL")
            {
                args = genExprs(s.args as P_Root.Exprs);
            }
            if (s.aout.Symbol.ToString() != "NIL")
            {
                var a = symbolTable.GetVarName(getString((s.aout as P_Root.Name).name));
                aout = new FSharpOption<string>(a);
            }
            return Syntax.Stmt.NewFunStmt(n, args, aout) as Syntax.Stmt.FunStmt;
        }

        private Syntax.Stmt genNulStmt(P_Root.NulStmt s)
        {
            if (s.op.Symbol.ToString() == "POP")
                return Syntax.Stmt.Pop;
            else if (s.op.Symbol.ToString() == "SKIP")
                return Syntax.Stmt.NewSkip("",-1,-1);
            return Syntax.Stmt.NewSkip("", -1, -1);
        }

        private Syntax.Stmt genBinStmt(P_Root.BinStmt s)
        {
            var arg1 = genLVal(s.arg1 as P_Root.Expr);

            if (s.op.Symbol.ToString() == "REMOVE")
            {
                var arg2 = genExpr(s.arg2 as P_Root.Expr);
                return Syntax.Stmt.NewRemove(arg1, arg2);
            }
            else if (s.op.Symbol.ToString() == "ASSIGN")
            {
                var arg2 = genExpr(s.arg2 as P_Root.Expr);
                return Syntax.Stmt.NewAssign(arg1, arg2);
            }
            else if (s.op.Symbol.ToString() == "INSERT")
            {
                if (s.arg2 is P_Root.Tuple)
                {
                    var args = (s.arg2 as P_Root.Tuple).body as P_Root.Exprs;
                    var arg2 = genExpr(args.head as P_Root.Expr);
                    args = args.tail as P_Root.Exprs;
                    var arg3 = genExpr(args.head as P_Root.Expr);
                    if (args.tail.Symbol.ToString() == "NIL")
                        return Syntax.Stmt.NewInsert(arg1, arg2, arg3);
                }
                throw new InvalidOperationException("Bad insert op!");
            }
            return null;
        }

        private Syntax.Lval genLVal(P_Root.Expr e)
        {
            if (e is P_Root.Name)
            {
                var x = e as P_Root.Name;
                var n = symbolTable.GetVarName(getString(x.name));
                return Syntax.Lval.NewVar(n);
            }
            else if (e is P_Root.Field)
            {
                var x = e as P_Root.Field;
                var arg = genLVal(x.arg as P_Root.Expr);
                if (x.name is P_Root.Natural)
                {
                    var f = getValue(x.name as P_Root.Natural);
                    return Syntax.Lval.NewDot(arg, f);
                }
                else if (x.name is P_Root.String)
                {
                    var f = getString(x.name);
                    return Syntax.Lval.NewNamedDot(arg, f);
                }
                return null;
            }
            else if (e is P_Root.BinApp &&
                (e as P_Root.BinApp).op.Symbol.ToString() == "IDX")
            {
                var x = e as P_Root.BinApp;
                var arg1 = genLVal(x.arg1 as P_Root.Expr);
                var arg2 = genExpr(x.arg2 as P_Root.Expr);
                return Syntax.Lval.NewIndex(arg1, arg2);
            }
            return null;
        }

        private Syntax.Stmt.Return genReturnStmt(P_Root.Return s)
        {
            FSharpOption<Syntax.Expr> e = null;
            var refParams = functionsToRefParams[symbolTable.currentF];
            var retList = new List<Syntax.Expr>();

            foreach (var x in refParams)
            {
                retList.Add(Syntax.Expr.NewVar(x.Item2));
            }
            
            if (s.expr.Symbol.ToString() != "NIL")
            {
                var expr = genExpr(s.expr as P_Root.Expr);
                if(refParams.Count > 0)
                {
                    retList.Insert(0, expr);
                    e = new FSharpOption<Syntax.Expr>(Syntax.Expr.NewTuple(ListModule.OfSeq(retList)));
                }
                else    
                    e = new FSharpOption<Syntax.Expr>(expr);
            }
            else if(refParams.Count > 0)
            {
                e = new FSharpOption<Syntax.Expr>(Syntax.Expr.NewTuple(ListModule.OfSeq(retList)));
            }

            return Syntax.Stmt.NewReturn(e) as Syntax.Stmt.Return;
        }

        private Syntax.Stmt.While genWhileStmt(P_Root.While s)
        {
            var c = genExpr(s.cond as P_Root.Expr);
            var stLst = genStmt(s.body as P_Root.Stmt);
            var st = Syntax.Stmt.NewSeqStmt(ListModule.OfSeq(stLst));
            return Syntax.Stmt.NewWhile(c, st) as Syntax.Stmt.While;
        }

        private Syntax.Stmt.Ite genIteStmt(P_Root.Ite s)
        {
            var c = genExpr(s.cond as P_Root.Expr);
            var tLst = genStmt(s.@true as P_Root.Stmt);
            var fLst = genStmt(s.@false as P_Root.Stmt);
            var t = Syntax.Stmt.NewSeqStmt(ListModule.OfSeq(tLst));
            var f = Syntax.Stmt.NewSeqStmt(ListModule.OfSeq(fLst));
            return Syntax.Stmt.NewIte(c, t, f) as Syntax.Stmt.Ite;
        }

        private List<Syntax.Stmt> genStmtList(P_Root.Seq s)
        {
            var lst = new List<Syntax.Stmt>();
            var x = s;
            do
            {
                lst.AddRange(genStmt(x.s1 as P_Root.Stmt));
                if(x.s2 is P_Root.Seq) //Recursion - we have [s1, [s2, ... ]]
                    x = (x.s2 as P_Root.Seq);
                else //s2 is not a seq statement. Base case - We have [s1, s2]
                {
                    lst.AddRange(genStmt(x.s2 as P_Root.Stmt));
                    break;
                }
            }
            while (true);
            return lst;
        }
        private Syntax.Stmt genCaseBody(P_Root.AnonFunDecl d, ref string name)
        {
            FSharpOption<Syntax.Type> retType = null;
            FSharpOption<Syntax.Expr> retExp = null;
            List<Syntax.Stmt> body = new List<Syntax.Stmt>();
            var args = new List<Syntax.VarDecl>();

            var ln = getLineNumber(d.body as P_Root.Stmt);
            name += ln;
            if (ln == 0)
                name += ("_rand_" + r.Next());

            var env = symbolTable.IncludeSurroundingScopes(name);
            var envVarDecl = new Syntax.VarDecl(name + "_env", env.Item1);
            //Added this envVarDecl to PARENT FUNCTION - as NewScope() 
            //is called below.
            if(env.Item1.Item.Length > 0)
            {
                var cf = symbolTable.currentF;
                functionsToLocals[cf].Add(envVarDecl);
                args.Add(new Syntax.VarDecl(name + "_env", env.Item1));
                retExp = new FSharpOption<Syntax.Expr>(env.Item2 as Syntax.Expr);
                retType = new FSharpOption<Syntax.Type>(env.Item1);
                body.AddRange(env.Item4);
            }

            if (env.Item1.Item.Length > maxFields)
                maxFields = env.Item1.Item.Length;

            NewScope(name);
            
            //Get args            
            args.Insert(0, getAnonFunParams(d.envVars as P_Root.NmdTupType, name));

            //Get Locals
            functionsToLocals[name].AddRange(env.Item3);
            if (d.locals.Symbol.ToString() != "NIL")
            {
                functionsToLocals[name].AddRange(genVars(d.locals as P_Root.NmdTupType, name));
            }

            //Get Body Statements
            if (d.body is P_Root.Seq)
            {
                body.AddRange(genStmtList(d.body as P_Root.Seq));
            }
            else
            {
                body.AddRange(genStmt(d.body as P_Root.Stmt));
            }
            body.Add(Syntax.Stmt.NewReturn(retExp));

            //Make the Function Declaration.
            var fd = new Syntax.FunDecl(name, ListModule.OfSeq(args), retType,
                ListModule.OfSeq(functionsToLocals[name]),
                ListModule.OfSeq(body), false, false);

            //Add it to the relevant machine's table
            if (d.owner.Symbol.ToString() != "NIL")
            {
                machineToFunList[symbolTable.currentM].Add(fd);
            }
            else
            {
                staticFunctions.Add(fd);
            }
            ExitScope();

            var stmtList = new List<Syntax.Stmt>();
            var argList = new List<Syntax.Expr>();
            argList.Add(Syntax.Expr.NewVar("payload"));
            FSharpOption<string> retVar = null;

            if (env.Item1.Item.Length > 0)
            {
                argList.Add(env.Item2);
                retVar = new FSharpOption<string>(name + "_env");
            }
            stmtList.Add(Syntax.Stmt.NewFunStmt(name, ListModule.OfSeq(argList), retVar));
            stmtList.AddRange(env.Item4);
            return Syntax.Stmt.NewSeqStmt(ListModule.OfSeq(stmtList));
        }

        private Tuple<string, Syntax.Stmt> genCase(P_Root.Cases s)
        {
            var trig = getString(s.trig);
            string n = symbolTable.currentF + "_case_" + trig; ;
            var action = genCaseBody(s.action as P_Root.AnonFunDecl, ref n);
            return new Tuple<string, Syntax.Stmt>(trig, action);
        }

        private Syntax.Stmt.Receive genReceiveStmt(P_Root.Receive s)
        {
            var @case = s.cases as P_Root.Cases;
            var lst = new List<Tuple<string,Syntax.Stmt>>();
            do
            {
                lst.Add(genCase(@case));
                @case = @case.cases as P_Root.Cases;
            } while (@case != null);
            return Syntax.Stmt.NewReceive(ListModule.OfSeq(lst))
                as Syntax.Stmt.Receive;
        }

        private Syntax.Stmt.Assert genAssertStmt(P_Root.Assert s)
        {
            //Ignored msg - no need in a verifier.
            var arg = genExpr(s.arg as P_Root.Expr);
            return Syntax.Stmt.NewAssert(arg) as Syntax.Stmt.Assert;
        }

        private List<Syntax.Stmt> genStmt(P_Root.Stmt s)
        {
            var ln = getLineNumber(s);
            if (s is P_Root.NewStmt)
            {
                var st = genNewStmt(s as P_Root.NewStmt);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Raise)
            {
                var st = genRaiseStmt(s as P_Root.Raise);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Send)
            {
                var st = genSendStmt(s as P_Root.Send);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Monitor)
            {
                var st = genMonitorStmt(s as P_Root.Monitor);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.FunStmt)
            {
                var st = genFunStmt(s as P_Root.FunStmt);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.NulStmt)
            {
                var st = genNulStmt(s as P_Root.NulStmt);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.BinStmt)
            {
                var st = genBinStmt(s as P_Root.BinStmt);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Return)
            {
                var st = genReturnStmt(s as P_Root.Return);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.While)
            {
                var st = genWhileStmt(s as P_Root.While);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Ite)
            {
                var st = genIteStmt(s as P_Root.Ite);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Seq)
            {
                var lst = genStmtList(s as P_Root.Seq);
                return lst;
            }
            else if (s is P_Root.Receive)
            {
                var st = genReceiveStmt(s as P_Root.Receive);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            else if (s is P_Root.Assert)
            {
                var st = genAssertStmt(s as P_Root.Assert);
                var lst = new List<Syntax.Stmt>();
                lst.Add(Syntax.Stmt.NewSkip(ln));
                lst.Add(st);
                return lst;
            }
            return null;
        }

        private Syntax.EventDecl genEventDecl(P_Root.EventDecl d)
        {
            var name = getString(d.name);
            FSharpOption<Syntax.Type> t = null;
            FSharpOption<Syntax.Card> c = null;
            if (d.type.Symbol.ToString() != "NIL")
            {
                var x = genTypeExpr(d.type as P_Root.TypeExpr);
                t = new FSharpOption<Syntax.Type>(x);
            }
            if (d.card.Symbol.ToString() != "NIL")
            {
                var x = genQueueConstraint(d.card as P_Root.QueueConstraint);
                c = new FSharpOption<Syntax.Card>(x);
            }
            return new Syntax.EventDecl(name, c, t);
        }

        private Syntax.MachineDecl genMachineDecl(P_Root.MachineDecl d)
        {
            string name = getString(d.name);
            string start_state = name + '_' +
                getQualifiedName(d.start as P_Root.QualifiedName);
            FSharpList<Syntax.StateDecl> states =
                ListModule.OfSeq(machineToStateList[name]);
            FSharpList<Syntax.VarDecl> globals =
                ListModule.OfSeq(machineToVars[name]);
            FSharpList<Syntax.FunDecl> functions =
                ListModule.OfSeq(machineToFunList[name]);
            bool is_monitor = false;
            bool is_model = false;
            FSharpList<string> monitored_events = FSharpList<string>.Empty;
            FSharpOption<Syntax.Card> qc = null;

            if (d.isMain.Symbol.ToString() == "TRUE")
                mainMachine = name;
            if (d.kind.Symbol.ToString() == "MODEL")
                is_model = true;
            else if (d.kind.Symbol.ToString() == "MONITOR")
            {
                is_monitor = true;
                monitored_events =
                    ListModule.OfSeq(monitorToEventList[name]);
            }
            if (d.card.Symbol.ToString() != "NIL")
            {
                var x = genQueueConstraint(d.card as P_Root.QueueConstraint);
                qc = new FSharpOption<Syntax.Card>(x);
            }
            if (d.isMain.Symbol.ToString() == "TRUE")
                mainMachine = name;

            return new Syntax.MachineDecl(name, start_state, globals, functions,
                states, is_monitor, monitored_events, qc, is_model, hasPush);
        }

        private Syntax.Card genQueueConstraint(P_Root.QueueConstraint qc)
        {
            if (qc is P_Root.AssertMaxInstances)
            {
                var x = qc as P_Root.AssertMaxInstances;
                var bound = getValue(x.bound);
                return Syntax.Card.NewAssert(bound);
            }
            else if (qc is P_Root.AssumeMaxInstances)
            {
                var x = qc as P_Root.AssumeMaxInstances;
                var bound = getValue(x.bound);
                return Syntax.Card.NewAssume(bound);
            }
            return null;
        }

        private Syntax.VarDecl genVarDecl(P_Root.VarDecl d)
        {
            var n = getString(d.name);
            var owner = getString((d.owner as P_Root.MachineDecl).name);
            var t = genTypeExpr(d.type as P_Root.TypeExpr);
            symbolTable.AddMachVar(owner, n, t); //For reference in future statements.
            n = owner + '_' + n;
            return new Syntax.VarDecl(n, t);
        }

        private Syntax.StateDecl genStateDecl(P_Root.StateDecl state)
        {
            string temperature = state.temperature.Symbol.ToString();
            temperature = char.ToUpper(temperature[0]) + temperature.Substring(1);
            var owner = getString((state.owner as P_Root.MachineDecl).name);
            var name = owner + '_' + getQualifiedName(state.name as P_Root.QualifiedName);
            FSharpOption<string> entryAction = null;
            FSharpOption<string> exitAction = null;

            if (state.entryAction is P_Root.AnonFunDecl)
            {
                var s = name + "_entry";
                genAnonFunDecl(state.entryAction as P_Root.AnonFunDecl, ref s);
                entryAction = new FSharpOption<string>(s);
            }
            else if (state.entryAction is P_Root.String)
            {
                //A special case. We generate a FunDecl 
                //which calls the function in question.
                var action = name + "_entry";
                var funName = symbolTable.GetFunName(getString(state.entryAction));
                var @params = new FSharpList<Syntax.VarDecl>(new Syntax.VarDecl("payload", Syntax.Type.Null),
                    FSharpList<Syntax.VarDecl>.Empty);
                var body = new FSharpList<Syntax.Stmt>(Syntax.Stmt.NewFunStmt(funName, FSharpList<Syntax.Expr>.Empty, null),
                    FSharpList<Syntax.Stmt>.Empty);
                var fd = new Syntax.FunDecl(action, @params, null, FSharpList<Syntax.VarDecl>.Empty, body, false, false);
                machineToFunList[symbolTable.currentM].Add(fd);
                entryAction = new FSharpOption<string>(action);
            }

            if (state.exitFun is P_Root.AnonFunDecl)
            {
                var s = name + "_exit";
                genAnonFunDecl(state.exitFun as P_Root.AnonFunDecl, ref s);
                exitAction = new FSharpOption<string>(s);
            }
            else if (state.exitFun is P_Root.String)
            {
                //A special case. We generate a FunDecl 
                //which calls the function in question.
                var action = name + "_exit";
                var funName = symbolTable.GetFunName(getString(state.exitFun));
                var @params = new FSharpList<Syntax.VarDecl>(new Syntax.VarDecl("payload", Syntax.Type.Null),
                    FSharpList<Syntax.VarDecl>.Empty);
                var body = new FSharpList<Syntax.Stmt>(Syntax.Stmt.NewFunStmt(funName, FSharpList<Syntax.Expr>.Empty, null),
                    FSharpList<Syntax.Stmt>.Empty);
                var fd = new Syntax.FunDecl(action, @params, null, FSharpList<Syntax.VarDecl>.Empty, body, false, false);
                machineToFunList[symbolTable.currentM].Add(fd);
                exitAction = new FSharpOption<string>(action);
            }
            var transitions = ListModule.OfSeq(statesToTransitions[name]);
            var Dos = ListModule.OfSeq(statesToDos[name]);
            return new Syntax.StateDecl(name, temperature, entryAction, exitAction, transitions, Dos);
        }

        private Syntax.VarDecl genVar(P_Root.NmdTupTypeField n, string owner)
        {
            var name = getString(n.name);
            var type = genTypeExpr(n.type as P_Root.TypeExpr);
            symbolTable.AddVar(name, type);
            name = owner + '_' + name;
            return new Syntax.VarDecl(name, type);
        }

        private List<Syntax.VarDecl> genVars(P_Root.NmdTupType n, string owner)
        {
            var lst = new List<Syntax.VarDecl>();
            var x = n;
            do
            {
                var d = genVar(x.hd as P_Root.NmdTupTypeField, owner);
                lst.Add(d);
                x = x.tl as P_Root.NmdTupType;
            } while (x != null);

            return lst;
        }

        private FSharpList<Syntax.VarDecl> getFunParams(P_Root.NmdTupType p, string owner)
        {
            var lst = new List<Syntax.VarDecl>();
            var x = p;
            int i = 0;
            do
            {
                var f = x.hd as P_Root.NmdTupTypeField;
                var d = genVar(f, owner);
                if(f.qual.Symbol.ToString() == "REF")
                {
                    var cf = symbolTable.currentF;
                    functionsToRefParams[cf].Add(new Tuple<int, string, Syntax.Type>(i, d.Name, d.Type));
                }
                lst.Add(d);
                x = x.tl as P_Root.NmdTupType;
                i++;
            } while (x != null);

            return ListModule.OfSeq(lst);
        }

        private List<Syntax.VarDecl> genFunParams(P_Root.NmdTupType n, string owner)
        {
            var lst = new List<Syntax.VarDecl>();
            var x = n;
            int i = 0;
            do
            {
                var p = x.hd as P_Root.NmdTupTypeField;
                var d = genVar(p, owner);
                if (p.qual.Symbol.ToString() == "REF")
                    functionsToRefParams[owner].Add(
                        new Tuple<int, string, Syntax.Type>(i, d.Name, d.Type));
                lst.Add(d);
                x = x.tl as P_Root.NmdTupType;
                ++i;
            } while (x != null);

            return lst;
        }

        private Syntax.FunDecl genFunDecl(P_Root.FunDecl d)
        {
            var name = symbolTable.GetFunName(getString(d.name));
            NewScope(name);
            name =symbolTable.GetFunName(name);
            bool is_model = false;
            bool is_pure = false;
            FSharpOption<Syntax.Type> rettype = null;
            FSharpList<Syntax.VarDecl> @params = FSharpList<Syntax.VarDecl>.Empty;
            var typLst = new List<Syntax.Type>();
            if (d.kind.Symbol.ToString() == "MODEL")
            {
                is_model = true;
            }
            else if (d.kind.Symbol.ToString() == "PURE")
            {
                is_pure = true;
            }
            if (d.@params.Symbol.ToString() != "NIL")
            {
                @params = ListModule.OfSeq(genFunParams(d.@params as P_Root.NmdTupType, name));
            }
            if (d.locals.Symbol.ToString() != "NIL")
            {
                functionsToLocals[name].AddRange
                    (genVars(d.locals as P_Root.NmdTupType, name));
            }

            var stmt = ListModule.OfSeq(genStmt(d.body as P_Root.Stmt));

            //Return type.
            foreach(var x in functionsToRefParams[name])
            {
                typLst.Add(x.Item3);
            }

            if (d.@return.Symbol.ToString() != "NIL")
            {
                var x = genTypeExpr(d.@return as P_Root.TypeExpr);
                if (typLst.Count > 0)
                {
                    typLst.Insert(0, x);
                    rettype = new FSharpOption<Syntax.Type>(
                        Syntax.Type.NewTuple(ListModule.OfSeq(typLst)));
                }
                else
                    rettype = new FSharpOption<Syntax.Type>(x);
            }
            else if(typLst.Count > 0)
            {
                rettype = new FSharpOption<Syntax.Type>(
                    Syntax.Type.NewTuple(ListModule.OfSeq(typLst)));
            }

            ExitScope();
            var locals = ListModule.OfSeq(functionsToLocals[name]);
            return new Syntax.FunDecl(name, @params, rettype, locals, stmt, is_model, is_pure);
        }

        //Check if the params are called _payload_0, _payload_skip... etc.
        //If not, add them to the param list.
        private Syntax.VarDecl getAnonFunParams(P_Root.NmdTupType x, string owner)
        {
            while (x.tl.Symbol.ToString() != "NIL")
            {
                x = x.tl as P_Root.NmdTupType;
            }
            var n = x.hd as P_Root.NmdTupTypeField;

            var name = getString(n.name);
            var type = genTypeExpr(n.type as P_Root.TypeExpr);
           
            symbolTable.AddVar(name, type);
            name = owner + '_' + name;
            return new Syntax.VarDecl(name, type);
        }

        //A(sad?) Departure from Design. 
        //We generate the name of the AnonFunction, a FunDecl to
        //that effect and add it to the appropriate list.
        private void genAnonFunDecl(P_Root.AnonFunDecl d, ref string name)
        {
            FSharpOption<Syntax.Type> retType = null;
            FSharpOption<Syntax.Expr> retExp = null;
            List<Syntax.Stmt> body = new List<Syntax.Stmt>();

            var ln = getLineNumber(d.body as P_Root.Stmt);
            name += ln;
            if (ln == 0)
                name += ("_rand_" + r.Next());

            if (!symbolTable.InsideStaticFn)
                symbolTable.AddMachFun(symbolTable.currentM, name); 

            NewScope(name);
            //Get args
            var args = new List<Syntax.VarDecl>();
            args.Add(getAnonFunParams(d.envVars as P_Root.NmdTupType, name));

            //Get Locals
            if (d.locals.Symbol.ToString() != "NIL")
            {
                functionsToLocals[name].AddRange(genVars(d.locals as P_Root.NmdTupType, name));
            }

            //Get Body Statements
            if (d.body is P_Root.Seq)
            {
                body.AddRange(genStmtList(d.body as P_Root.Seq));
            }
            else
            {
                body.AddRange(genStmt(d.body as P_Root.Stmt));
            }
            body.Add(Syntax.Stmt.NewReturn(retExp));

            //Make the Function Declaration.
            var fd = new Syntax.FunDecl(name, ListModule.OfSeq(args), retType, ListModule.OfSeq(functionsToLocals[name]),
                ListModule.OfSeq(body), false, false);

            //Add it to the relevant machine's table
            if (d.owner.Symbol.ToString() != "NIL")
            {
                machineToFunList[symbolTable.currentM].Add(fd);
            }
            else
            {
                staticFunctions.Add(fd);
            }
            ExitScope();
        }

        private string genTrig(ICSharpTerm t)
        {
            if (t.Symbol.ToString() == "NULL")
            {
                return "null";
            }
            else if (t.Symbol.ToString() == "HALT")
            {
                return "halt";
            }
            else
            {
                return getString(t);
            }
        }

        private Syntax.TransDecl.T genTransDecl(P_Root.TransDecl t)
        {
            var trig = genTrig(t.trig);
            var src = (t.src as P_Root.StateDecl);
            var machName = getString((src.owner as P_Root.MachineDecl).name);
            symbolTable.currentM = machName;
            var owner = machName + '_' + getQualifiedName(src.name as P_Root.QualifiedName);
            var dst = machName + '_' + getQualifiedName(t.dst as P_Root.QualifiedName);
            if (t.action.Symbol.ToString() == "PUSH")
            {
                hasPush = true;
                return Syntax.TransDecl.T.NewPush(trig, dst);
            }
            else if (t.action is P_Root.AnonFunDecl)
            {
                var action = owner + "_on_" + trig + "_goto_" + dst;
                genAnonFunDecl(t.action as P_Root.AnonFunDecl, ref action);
                return Syntax.TransDecl.T.NewCall(trig, dst, action);
            }
            else
            {
                //A special case. We generate a FunDecl 
                //which calls the function in question.
                var action = owner + "_on_" + trig + "_goto_" + dst;
                var funName = symbolTable.GetFunName(getString(t.action));
                var @params = new FSharpList<Syntax.VarDecl>(new Syntax.VarDecl("payload", Syntax.Type.Null),
                    FSharpList<Syntax.VarDecl>.Empty);
                var body = new FSharpList<Syntax.Stmt>(Syntax.Stmt.NewFunStmt(funName, FSharpList<Syntax.Expr>.Empty, null),
                    FSharpList<Syntax.Stmt>.Empty);
                var fd = new Syntax.FunDecl(action, @params, null, FSharpList<Syntax.VarDecl>.Empty, body, false, false);
                machineToFunList[symbolTable.currentM].Add(fd);
                return Syntax.TransDecl.T.NewCall(trig, dst, action);
            }
        }

        private Syntax.DoDecl.T genDoDecl(P_Root.DoDecl d)
        {
            var st = (d.src as P_Root.StateDecl);
            var machName = getString((st.owner as P_Root.MachineDecl).name);
            var owner = machName + '_' + getQualifiedName(st.name as P_Root.QualifiedName);
            symbolTable.currentM = machName;
            var trig = genTrig(d.trig);
            if (d.action.Symbol.ToString() == "DEFER")
            {
                hasDefer = true;
                return Syntax.DoDecl.T.NewDefer(trig);
            }
            else if (d.action.Symbol.ToString() == "IGNORE")
            {
                hasIgnore = true;
                return Syntax.DoDecl.T.NewIgnore(trig);
            }
            else if (d.action is P_Root.AnonFunDecl)
            {
                var action = owner + "_do_" + trig;
                genAnonFunDecl(d.action as P_Root.AnonFunDecl, ref action);
                return Syntax.DoDecl.T.NewCall(trig, action);
            }
            else
            {
                //A special case. We generate a FunDecl 
                //which calls the function in question.
                var action = owner + "_do_" + trig;
                var funName = symbolTable.GetFunName(getString(d.action));
                var @params = new FSharpList<Syntax.VarDecl>(new Syntax.VarDecl("payload", Syntax.Type.Null),
                    FSharpList<Syntax.VarDecl>.Empty);
                var body = new FSharpList<Syntax.Stmt>(Syntax.Stmt.NewFunStmt(funName, FSharpList<Syntax.Expr>.Empty, null),
                    FSharpList<Syntax.Stmt>.Empty);
                var fd = new Syntax.FunDecl(action, @params, null, FSharpList<Syntax.VarDecl>.Empty, body, false, false);
                machineToFunList[symbolTable.currentM].Add(fd);
                return Syntax.DoDecl.T.NewCall(trig, action);
            }
        }

        /* ToDo
        private void genAnnotatable(P_Root.Annotatable a)
        {
            if (a is P_Root.EventDecl)
            {
                genEventDecl(a as P_Root.EventDecl);
            }
            else if (a is P_Root.MachineDecl)
            {
                genMachineDecl(a as P_Root.MachineDecl);
            }
            else if (a is P_Root.VarDecl)
            {
                genVarDecl(a as P_Root.VarDecl);
            }
            else if (a is P_Root.FunDecl)
            {
                genFunDecl(a as P_Root.FunDecl);
            }
            else if (a is P_Root.StateDecl)
            {
                genStateDecl(a as P_Root.StateDecl);
            }
            else if (a is P_Root.TransDecl)
            {
                genTransDecl(a as P_Root.TransDecl);
            }
            else if (a is P_Root.DoDecl)
            {
                genDoDecl(a as P_Root.DoDecl);
            }
        }

        private void genAnnotation(P_Root.Annotation a)
        {
            genAnnotatable(a.ant as P_Root.Annotatable);
            //ToDo Assertion Generation Logic.
        }*/
        private void addTypeDef(P_Root.TypeDef t)
        {
            var type = genTypeExpr(t.type as P_Root.TypeExpr);
            if (type != null)
            {
                var n = getString(t.name);
                typeDefs[n] = type;
            }
            return;
        }

        private void addTypeDefs(List<P_Root.TypeDef> tdLst)
        {
            var iter = true;
            while (iter)
            {
                iter = false;
                foreach (var t in tdLst)
                {
                    var k = getString(t.name);
                    if (!typeDefs.ContainsKey(k))
                    {
                        iter = true;
                        addTypeDef(t);
                    }
                }
            }
        }

        private void fixTypeDefs()
        {
            var tdLst = new List<P_Root.TypeDef>();
            foreach (var program in parsedPrograms)
            {
                tdLst.AddRange(program.TypeDefs);
            }
            addTypeDefs(tdLst);
        }

        private void ClearAll()
        {
            statesToDos.Clear();
            statesToTransitions.Clear();

            machineToStateList.Clear();
            machineToFunList.Clear();
            machineToVars.Clear();
            monitorToEventList.Clear();

            staticFunctions.Clear();
            machines.Clear();
            events.Clear();
            mainMachine = null;
            typeDefs.Clear();
            symbolTable.Clear();
            eventToMonitorList.Clear();

            events.Add(new Syntax.EventDecl("halt", null, null));
            events.Add(new Syntax.EventDecl("null", null, null));

            maxFields = 0;
            hasDefer = false;
            hasIgnore = false;
    }

        private void Init()
        {
            ClearAll();
            foreach (var program in parsedPrograms)
            {
                var file = program.FileInfos;
                foreach (var state in program.States)
                {
                    var name = getString((state.owner as P_Root.MachineDecl).name)
                        + '_'
                        + getQualifiedName(state.name as P_Root.QualifiedName);
                    // Console.WriteLine(name);
                    statesToDos[name] = new List<Syntax.DoDecl.T>();
                    statesToTransitions[name] = new List<Syntax.TransDecl.T>();
                }

                foreach (var machine in program.Machines)
                {
                    var name = getString(machine.name);
                    machineToStateList[name] = new List<Syntax.StateDecl>();
                    machineToFunList[name] = new HashSet<Syntax.FunDecl>();
                    machineToVars[name] = new List<Syntax.VarDecl>();
                    monitorToEventList[name] = new List<string>();
                    symbolTable.AddMachine(name);
                }

                foreach (var fun in program.Functions)
                {
                    var name = getString(fun.name);
                    if(fun.owner.Symbol.ToString() != "NIL")
                    {
                        var owner = getString((fun.owner as P_Root.MachineDecl).name);
                        symbolTable.AddMachFun(owner, name);
                    }
                }

                foreach(var ev in program.Events)
                {
                    var evName = getString(ev.name);
                    eventToMonitorList[evName] = new List<string>();
                }
                eventToMonitorList["null"] = new List<string>();
                eventToMonitorList["halt"] = new List<string>();
            }
        }

        private void genFSExprs()
        {
            foreach (var program in parsedPrograms)
            {
                foreach (var ev in program.Events)
                {
                    var e = genEventDecl(ev);
                    events.Add(e);
                    eventsToDecls[e.Name] = e;
                }

                foreach (var vd in program.Variables)
                {
                    var v = genVarDecl(vd);
                    var owner = getString((vd.owner as P_Root.MachineDecl).name);
                    machineToVars[owner].Add(v);
                }

                foreach (var function in program.Functions)
                {
                    if (function.owner.Symbol.ToString() == "NIL")
                    {
                        symbolTable.InsideStaticFn = true;
                        var f = genFunDecl(function);
                        staticFunctions.Add(f);
                    }
                    else
                    {
                        symbolTable.InsideStaticFn = false;
                        var m = function.owner as P_Root.MachineDecl;
                        string n = getString(m.name);
                        symbolTable.currentM = n;
                        var f = genFunDecl(function);
                        machineToFunList[n].Add(f);
                    }
                }

                symbolTable.InsideStaticFn = false;

                foreach (var doDecl in program.Dos)
                {
                    var s = doDecl.src as P_Root.StateDecl;
                    var currentM = getString((s.owner as P_Root.MachineDecl).name);
                    symbolTable.currentM = currentM;
                    string n = currentM + '_' + 
                        getQualifiedName(s.name as P_Root.QualifiedName);
                    var x = genDoDecl(doDecl);
                    statesToDos[n].Add(x);
                }

                foreach (var trans in program.Transitions)
                {
                    var s = trans.src as P_Root.StateDecl;
                    var currentM = getString((s.owner as P_Root.MachineDecl).name);
                    string n = currentM + '_' +
                        getQualifiedName(s.name as P_Root.QualifiedName);
                    symbolTable.currentM = currentM;
                    var x = genTransDecl(trans);
                    statesToTransitions[n].Add(x);
                }

                foreach (var state in program.States)
                {
                    var m = state.owner as P_Root.MachineDecl;
                    string n = getString(m.name);
                    symbolTable.currentM = n;
                    var s = genStateDecl(state);
                    machineToStateList[n].Add(s);
                }

                foreach (var obs in program.Observes)
                {
                    var ev = getString(obs.ev);
                    var n = (obs.monitor as P_Root.MachineDecl).name;
                    string mName = getString(n);
                    monitorToEventList[mName].Add(ev);
                    eventToMonitorList[ev].Add(mName);
                }

                foreach (var machine in program.Machines)
                {
                    string n = getString(machine.name);
                    symbolTable.currentM = n;
                    machines.Add(genMachineDecl(machine));
                }
            }
        }

        private bool ReadFile(string inputFileName)
        {
            var result = compiler.Compile(inputFileName);

            if (result)
            {
                parsedPrograms = new List<PProgram>(compiler.ParsedPrograms.Values);
                Init();
                //Get all TypeDefs first.
                fixTypeDefs();
                return true;
            }
            else
            {
                Console.WriteLine("Compilation failed. Compile from command line to see detailed error messages. Terminating...");
                return false;
            }

        }

        public Syntax.ProgramDecl genFSExpression(string inputFileName)
        {
            //Read the file and parse it. If it's good, go ahead and emit code.
            if (!ReadFile(inputFileName))
            {
                Environment.Exit(-1);
            }
            fileName = Path.GetFullPath(inputFileName);
            genFSExprs();
            var evMonList = new List<Tuple<string, FSharpList<string>>>();
            foreach(var kv in eventToMonitorList)
            {
                evMonList.Add(new Tuple<string, FSharpList<string>>(kv.Key, ListModule.OfSeq(kv.Value)));
            }     
            var prog =  new Syntax.ProgramDecl(fileName, mainMachine,
                ListModule.OfSeq(machines), ListModule.OfSeq(events), MapModule.OfSeq(evMonList),
                ListModule.OfSeq(staticFunctions), maxFields, hasDefer, hasIgnore);
            var map = new List<Tuple<string, FSharpList<Tuple<int, string, Syntax.Type>>>>();
            foreach (var kv in functionsToRefParams)
            {
                map.Add(new Tuple<string, FSharpList<Tuple<int, string, Syntax.Type>>>
                    (kv.Key, ListModule.OfSeq(kv.Value)));
            }
            return RemoveRefParams.removeRefParamsProgram(MapModule.OfSeq(map), prog);
        }
    }
}