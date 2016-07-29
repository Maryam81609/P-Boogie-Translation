namespace Microsoft.P2Boogie

//Helper module to flatten all sequences of sequences. 
//For aesthetic purposes, for now at least.
module FlattenStmtLists = 
  open Syntax
  open Common

  let rec flattenStmt st =
    match st with
    | Assign(_) | Insert(_)
    | Remove(_)
    | Assert(_)
    | Assume(_)
    | NewStmt(_)
    | Raise(_)
    | Send(_)
    | Skip(_)
    | Pop
    | Return(_)
    | Monitor(_)
    | FunStmt(_) -> [st]
    | While(c, s) -> [While(c, (flattenAllStmts(flattenStmt s)))]
    | Ite(c, i, e) -> 
      [Ite(c, (flattenAllStmts(flattenStmt i)), (flattenAllStmts(flattenStmt e)))]
    | SeqStmt(ls) -> 
      List.fold (fun acc s -> acc @ (flattenStmt s)) [] ls
    | Receive(ls) -> 
        [Receive(List.map (fun (e, st) -> (e, flattenAllStmts(flattenStmt st))) ls)]
      
  and flattenAllStmts stlst = 
    match stlst with
    | [s] -> s
    | h::t -> SeqStmt(stlst)
    | _ -> raise NotDefined
  
  let flattenStmtsFun (fd: FunDecl) = 
    let flatSt = List.fold (fun acc st -> acc @ (flattenStmt st)) [] fd.Body
    new FunDecl(fd.Name, fd.Formals, fd.RetType, fd.Locals, flatSt, fd.IsModel, fd.IsPure)
  
  let flattenStmtsMachine (md: MachineDecl) = 
    let fLst = List.map flattenStmtsFun md.Functions
    new MachineDecl(md.Name, md.StartState, md.Globals, fLst, md.States, md.IsMonitor, md.MonitorList, md.QC, md.IsModel, md.HasPush)

  let flattenStmtsProg (prog: ProgramDecl) = 
    let fLst = List.map flattenStmtsFun prog.StaticFuns
    let mLst = List.map flattenStmtsMachine prog.Machines
    new ProgramDecl(prog.FileName, prog.MainMachine, prog.Machines, prog.Events, prog.EventsToMonitors, prog.StaticFuns, prog.maxFields, prog.HasDefer, prog.HasIgnore)

