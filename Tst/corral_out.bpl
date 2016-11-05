type PrtType;

const unique PrtTypeNull: PrtType;

const unique PrtTypeInt: PrtType;

const unique PrtTypeBool: PrtType;

const unique PrtTypeMachine: PrtType;

const unique PrtTypeEvent: PrtType;

const unique PrtTypeTuple1: PrtType;

type PrtRef;

const unique null: PrtRef;

const unique PrtTrue: PrtRef;

const unique PrtFalse: PrtRef;

function PrtDynamicType(PrtRef) : PrtType;

function PrtIsNull(PrtRef) : bool;

function PrtFieldInt(PrtRef) : int;

function PrtFieldBool(PrtRef) : bool;

function PrtFieldMachine(PrtRef) : int;

function PrtFieldEvent(PrtRef) : int;

function PrtFieldTuple0(PrtRef) : PrtRef;

function PrtFieldSeqStore(PrtRef) : [int]PrtRef;

function PrtFieldSeqSize(PrtRef) : int;

function PrtFieldMapKeys(PrtRef) : [int]PrtRef;

function PrtFieldMapValues(PrtRef) : [int]PrtRef;

function PrtFieldMapSize(PrtRef) : int;

axiom PrtDynamicType(null) == PrtTypeNull;

axiom PrtIsNull(null) <==> true;

axiom (forall x: PrtRef :: { PrtIsNull(x) } x == null || !PrtIsNull(x));

function PrtConstructFromInt(int) : PrtRef;

axiom (forall x: int :: { PrtFieldInt(PrtConstructFromInt(x)) } PrtFieldInt(PrtConstructFromInt(x)) == x);

axiom (forall x: int :: { PrtDynamicType(PrtConstructFromInt(x)) } PrtDynamicType(PrtConstructFromInt(x)) == PrtTypeInt);

function {:inline} PrtConstructFromBool(v: bool) : PrtRef
{
  (if v then PrtTrue else PrtFalse)
}

axiom PrtFieldBool(PrtTrue);

axiom !PrtFieldBool(PrtFalse);

axiom PrtDynamicType(PrtTrue) == PrtTypeBool;

axiom PrtDynamicType(PrtFalse) == PrtTypeBool;

function PrtConstructFromMachineId(int) : PrtRef;

axiom (forall x: int :: { PrtFieldMachine(PrtConstructFromMachineId(x)) } PrtFieldMachine(PrtConstructFromMachineId(x)) == x);

axiom (forall x: int :: { PrtDynamicType(PrtConstructFromMachineId(x)) } PrtDynamicType(PrtConstructFromMachineId(x)) == PrtTypeMachine);

function PrtConstructFromEventId(int) : PrtRef;

axiom (forall x: int :: { PrtFieldEvent(PrtConstructFromEventId(x)) } PrtFieldEvent(PrtConstructFromEventId(x)) == x);

axiom (forall x: int :: { PrtDynamicType(PrtConstructFromEventId(x)) } PrtDynamicType(PrtConstructFromEventId(x)) == PrtTypeEvent);

procedure {:allocator} AllocatePrtRef() returns (x: PrtRef);



function {:inline} SeqIndexInBounds(seq: PrtRef, index: int) : bool
{
  0 <= index && index < PrtFieldSeqSize(seq)
}

function {:inline} ReadSeq(seq: PrtRef, index: int) : PrtRef
{
  PrtFieldSeqStore(seq)[index]
}

var {:thread_local} Main_x: PrtRef;

var {:thread_local} registerEvents: [int][int]bool;

var {:thread_local} tmpRhsValue: PrtRef;

var {:thread_local} tmpRhsValue_0: PrtRef;

procedure monitor(event: int, payload: PrtRef);



implementation monitor(event: int, payload: PrtRef)
{

  anon0:
    goto anon10_Then, anon10_Else;

  anon10_Then:
    assume {:partition} event == 0;
    goto anon2;

  anon10_Else:
    assume {:partition} event != 0;
    goto anon2;

  anon2:
    goto anon11_Then, anon11_Else;

  anon11_Then:
    assume {:partition} event == 1;
    goto anon4;

  anon11_Else:
    assume {:partition} event != 1;
    goto anon4;

  anon4:
    goto anon12_Then, anon12_Else;

  anon12_Then:
    assume {:partition} event == 2;
    goto anon6;

  anon12_Else:
    assume {:partition} event != 2;
    goto anon6;

  anon6:
    goto anon13_Then, anon13_Else;

  anon13_Then:
    assume {:partition} event == 3;
    goto anon8;

  anon13_Else:
    assume {:partition} event != 3;
    goto anon8;

  anon8:
    goto anon14_Then, anon14_Else;

  anon14_Then:
    assume {:partition} event == 4;
    return;

  anon14_Else:
    assume {:partition} event != 4;
    return;
}



procedure AssertPayloadDynamicType(event: PrtRef, payload: PrtRef) returns (evID: int);



procedure PrtEquals(a: PrtRef, b: PrtRef) returns (v: PrtRef);



procedure PrtEqualsTuple1(x: PrtRef, y: PrtRef) returns (v: PrtRef);



procedure Dequeue() returns (event: int, payload: PrtRef);
  modifies eventRaised, machineEvToQCount, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



implementation Dequeue() returns (event: int, payload: PrtRef)
{
  var ptr: int;
  var head: int;
  var tail: int;
  var q: int;

  anon0:
    goto anon11_Then, anon11_Else;

  anon11_Then:
    assume {:partition} eventRaised;
    eventRaised := false;
    event := raisedEvent;
    payload := raisedEventPl;
    return;

  anon11_Else:
    assume {:partition} !eventRaised;
    goto anon2;

  anon2:
    head := MachineInboxHead[thisMid];
    tail := MachineInboxTail[thisMid];
    ptr := head;
    event := 0 - 1;
    goto anon12_LoopHead;

  anon12_LoopHead:
    goto anon12_LoopDone, anon12_LoopBody;

  anon12_LoopBody:
    assume {:partition} ptr <= tail;
    event := MachineInboxStoreEvent[thisMid][ptr];
    goto anon13_Then, anon13_Else;

  anon13_Then:
    assume {:partition} event >= 0;
    q := machineEvToQCount[thisMid][event];
    machineEvToQCount[thisMid][event] := q - 1;
    goto anon14_Then, anon14_Else;

  anon14_Then:
    assume {:partition} ptr == head;
    MachineInboxHead[thisMid] := head + 1;
    goto anon8;

  anon14_Else:
    assume {:partition} ptr != head;
    goto anon15_Then, anon15_Else;

  anon15_Then:
    assume {:partition} ptr == tail;
    MachineInboxTail[thisMid] := tail - 1;
    goto anon8;

  anon15_Else:
    assume {:partition} ptr != tail;
    MachineInboxStoreEvent[thisMid][ptr] := 0 - 1;
    goto anon8;

  anon8:
    payload := MachineInboxStorePayload[thisMid][ptr];
    goto anon10;

  anon13_Else:
    assume {:partition} 0 > event;
    goto anon9;

  anon9:
    ptr := ptr + 1;
    event := 0 - 1;
    goto anon12_LoopHead;

  anon12_LoopDone:
    assume {:partition} tail < ptr;
    goto anon10;

  anon10:
    assume event >= 0;
    return;
}



procedure AssertEventCard(mid: int, event: int);



implementation AssertEventCard(mid: int, event: int)
{
  var head: int;
  var tail: int;
  var count: int;

  anon0:
    head := MachineInboxHead[mid];
    tail := MachineInboxTail[mid];
    count := machineEvToQCount[mid][event];
    goto anon10_Then, anon10_Else;

  anon10_Then:
    assume {:partition} event == 0;
    goto anon2;

  anon10_Else:
    assume {:partition} event != 0;
    goto anon2;

  anon2:
    goto anon11_Then, anon11_Else;

  anon11_Then:
    assume {:partition} event == 1;
    goto anon4;

  anon11_Else:
    assume {:partition} event != 1;
    goto anon4;

  anon4:
    goto anon12_Then, anon12_Else;

  anon12_Then:
    assume {:partition} event == 2;
    goto anon6;

  anon12_Else:
    assume {:partition} event != 2;
    goto anon6;

  anon6:
    goto anon13_Then, anon13_Else;

  anon13_Then:
    assume {:partition} event == 3;
    goto anon8;

  anon13_Else:
    assume {:partition} event != 3;
    goto anon8;

  anon8:
    goto anon14_Then, anon14_Else;

  anon14_Then:
    assume {:partition} event == 4;
    return;

  anon14_Else:
    assume {:partition} event != 4;
    return;
}



procedure WriteSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef);



procedure RemoveSeq(seq: PrtRef, index: int) returns (nseq: PrtRef);



procedure InsertSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef);



procedure MapContainsKey(map: PrtRef, key: PrtRef) returns (v: bool);



procedure ReadMap(map: PrtRef, key: PrtRef) returns (value: PrtRef);



procedure MapGetKeys(map: PrtRef) returns (seq: PrtRef);



procedure MapGetValues(map: PrtRef) returns (seq: PrtRef);



procedure WriteMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef);



procedure InsertMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef);



procedure RemoveMap(map: PrtRef, key: PrtRef) returns (nmap: PrtRef);



var machineCounter: int;

var MachineInboxStoreEvent: [int][int]int;

var MachineInboxStorePayload: [int][int]PrtRef;

var MachineInboxHead: [int]int;

var MachineInboxTail: [int]int;

var machineToQCAssert: [int]int;

var machineToQCAssume: [int]int;

var machineEvToQCount: [int][int]int;

var {:thread_local} thisMid: int;

var {:thread_local} eventRaised: bool;

var {:thread_local} raisedEvent: int;

var {:thread_local} raisedEventPl: PrtRef;

var {:thread_local} tmpEventID: int;

procedure InitializeInbox(mid: int);



implementation {:ForceInline} InitializeInbox(mid: int)
{

  anon0:
    assume MachineInboxHead[mid] == 1;
    assume MachineInboxTail[mid] == 0;
    return;
}



type {:datatype} StateStackType;

function {:constructor} Nil() : StateStackType;

function {:constructor} Cons(state: int, stack: StateStackType) : StateStackType;

var {:thread_local} StateStack: StateStackType;

var {:thread_local} CurrState: int;

procedure StateStackPush(state: int);



procedure StateStackPop();



procedure AssertMachineQueueSize(mid: int);



implementation AssertMachineQueueSize(mid: int)
{
  var head: int;
  var tail: int;
  var size: int;
  var qc: int;

  anon0:
    head := MachineInboxHead[mid];
    tail := MachineInboxTail[mid];
    size := tail - head + 1;
    qc := machineToQCAssert[mid];
    goto anon4_Then, anon4_Else;

  anon4_Then:
    assume {:partition} qc > 0;
    assert size <= qc;
    goto anon2;

  anon4_Else:
    assume {:partition} 0 >= qc;
    goto anon2;

  anon2:
    qc := machineToQCAssume[mid];
    goto anon5_Then, anon5_Else;

  anon5_Then:
    assume {:partition} qc > 0;
    assume size <= qc;
    return;

  anon5_Else:
    assume {:partition} 0 >= qc;
    return;
}



procedure Enqueue(mid: int, event: int, payload: PrtRef);
  modifies MachineInboxTail, machineEvToQCount, MachineInboxStoreEvent, MachineInboxStorePayload;



implementation Enqueue(mid: int, event: int, payload: PrtRef)
{
  var q: int;
  var tail: int;

  anon0:
    tail := MachineInboxTail[mid] + 1;
    MachineInboxTail[mid] := tail;
    q := machineEvToQCount[mid][event] + 1;
    machineEvToQCount[mid][event] := q;
    MachineInboxStoreEvent[mid][tail] := event;
    MachineInboxStorePayload[mid][tail] := payload;
    call {:si_unique_call 0} AssertEventCard(mid, event);
    call {:si_unique_call 1} AssertMachineQueueSize(mid);
    return;
}



procedure {:yields} send(mid: int, event: int, payload: PrtRef);
  modifies MachineInboxTail, machineEvToQCount, MachineInboxStoreEvent, MachineInboxStorePayload;



implementation send(mid: int, event: int, payload: PrtRef)
{

  anon0:
    call {:si_unique_call 2} monitor(event, payload);
    yield;
    call {:si_unique_call 3} Enqueue(mid, event, payload);
    return;
}



procedure {:yields} newMachine_Main(entryArg: PrtRef) returns (m: PrtRef);
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, StateStack, CurrState, eventRaised, thisMid, Main_x, registerEvents, MachineInboxTail, MachineInboxStoreEvent, MachineInboxStorePayload, MachineInboxHead, raisedEvent, raisedEventPl, tmpRhsValue_0;



implementation newMachine_Main(entryArg: PrtRef) returns (m: PrtRef)
{
  var tmp: int;

  anon0:
    machineCounter := machineCounter + 1;
    tmp := machineCounter;
    call {:si_unique_call 4} InitializeInbox(tmp);
    machineToQCAssert[tmp] := 0 - 1;
    machineToQCAssume[tmp] := 0 - 1;
    machineEvToQCount[tmp][0] := 0;
    machineEvToQCount[tmp][1] := 0;
    machineEvToQCount[tmp][2] := 0;
    machineEvToQCount[tmp][3] := 0;
    machineEvToQCount[tmp][4] := 0;
    yield;
    async call {:si_unique_call 5} MachineThread_Main(tmp, entryArg);
    m := PrtConstructFromMachineId(tmp);
    return;
}



procedure {:yields} newMachine_B(entryArg: PrtRef) returns (m: PrtRef);
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, StateStack, CurrState, eventRaised, thisMid, registerEvents, raisedEvent, raisedEventPl, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent, tmpRhsValue_0;



implementation newMachine_B(entryArg: PrtRef) returns (m: PrtRef)
{
  var tmp: int;

  anon0:
    machineCounter := machineCounter + 1;
    tmp := machineCounter;
    call {:si_unique_call 6} InitializeInbox(tmp);
    machineToQCAssert[tmp] := 0 - 1;
    machineToQCAssume[tmp] := 0 - 1;
    machineEvToQCount[tmp][0] := 0;
    machineEvToQCount[tmp][1] := 0;
    machineEvToQCount[tmp][2] := 0;
    machineEvToQCount[tmp][3] := 0;
    machineEvToQCount[tmp][4] := 0;
    yield;
    async call {:si_unique_call 7} MachineThread_B(tmp, entryArg);
    m := PrtConstructFromMachineId(tmp);
    return;
}



procedure {:yields} Main_Init_entry11(actual_Main_Init_entry11__payload_0: PrtRef);
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, MachineInboxTail, MachineInboxStoreEvent, MachineInboxStorePayload, StateStack, CurrState, eventRaised, thisMid, registerEvents, raisedEvent, raisedEventPl, MachineInboxHead, tmpRhsValue_0;



implementation Main_Init_entry11(actual_Main_Init_entry11__payload_0: PrtRef)
{
  var Main_Init_entry11__payload_0: PrtRef;
  var Main_Init_entry11_b: PrtRef;
  var Tmp132: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    Main_Init_entry11__payload_0 := actual_Main_Init_entry11__payload_0;
    Main_Init_entry11_b := null;
    assume {:sourceloc "", 11, 7} true;
    call {:si_unique_call 8} Tmp132 := newMachine_B(null);
    Main_Init_entry11_b := Tmp132;
    assume {:sourceloc "", 12, 4} true;
    call {:si_unique_call 9} send(PrtFieldMachine(Main_Init_entry11_b), 1, null);
    return;
}



procedure Main_Init_exit11(actual_Main_Init_exit11__payload_skip: PrtRef);



implementation Main_Init_exit11(actual_Main_Init_exit11__payload_skip: PrtRef)
{
  var Main_Init_exit11__payload_skip: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    Main_Init_exit11__payload_skip := actual_Main_Init_exit11__payload_skip;
    assume {:sourceloc "", 11, 7} true;
    return;
}



procedure Main_ProbeStateStack(event: int);
  modifies CurrState, StateStack;



implementation Main_ProbeStateStack(event: int)
{

  anon0:
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} registerEvents[CurrState][event];
    return;

  anon6_Else:
    assume {:partition} !registerEvents[CurrState][event];
    goto anon2;

  anon2:
    goto anon7_LoopHead;

  anon7_LoopHead:
    goto anon7_LoopDone, anon7_LoopBody;

  anon7_LoopBody:
    assume {:partition} StateStack != Nil();
    call {:si_unique_call 10} Main_CallExitAction();
    CurrState := state#Cons(StateStack);
    StateStack := stack#Cons(StateStack);
    goto anon8_Then, anon8_Else;

  anon8_Then:
    assume {:partition} registerEvents[CurrState][event];
    return;

  anon8_Else:
    assume {:partition} !registerEvents[CurrState][event];
    goto anon7_LoopHead;

  anon7_LoopDone:
    assume {:partition} StateStack == Nil();
    goto anon5;

  anon5:
    return;
}



procedure Main_CallEntryAction(state: int, payload: PrtRef);



procedure Main_CallExitAction();



implementation Main_CallExitAction()
{

  anon0:
    goto anon2_Then, anon2_Else;

  anon2_Then:
    assume {:partition} CurrState == 0;
    call {:si_unique_call 11} Main_Init_exit11(null);
    return;

  anon2_Else:
    assume {:partition} CurrState != 0;
    return;
}



procedure {:yields} MachineThread_Main(mid: int, entryArg: PrtRef);
  modifies StateStack, CurrState, eventRaised, thisMid, Main_x, registerEvents, machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, MachineInboxTail, MachineInboxStoreEvent, MachineInboxStorePayload, MachineInboxHead, raisedEvent, raisedEventPl, tmpRhsValue_0;



implementation MachineThread_Main(mid: int, entryArg: PrtRef)
{
  var event: int;
  var payload: PrtRef;
  var depth: int;

  anon0:
    StateStack := Nil();
    CurrState := 0;
    eventRaised := false;
    thisMid := mid;
    Main_x := PrtConstructFromInt(0);
    registerEvents[0][0] := false;
    registerEvents[0][1] := false;
    registerEvents[0][2] := false;
    registerEvents[0][3] := false;
    registerEvents[0][4] := false;
    call {:si_unique_call 12} Main_Init_entry11(entryArg);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} true;
    yield;
    call {:si_unique_call 13} event, payload := Dequeue();
    call {:si_unique_call 14} Main_ProbeStateStack(event);
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} CurrState == 0;
    goto Main_Init;

  Main_Init:
    goto anon7_Then, anon7_Else;

  anon7_Then:
    assume {:partition} event == 3;
    return;

  anon7_Else:
    assume {:partition} event != 3;
    assert false;
    goto anon5_LoopHead;

  anon6_Else:
    assume {:partition} CurrState != 0;
    assume false;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} !true;
    return;
}



procedure B_Init_on_Unit_goto_B_X22(actual_B_Init_on_Unit_goto_B_X22__payload_skip: PrtRef);



implementation B_Init_on_Unit_goto_B_X22(actual_B_Init_on_Unit_goto_B_X22__payload_skip: PrtRef)
{
  var B_Init_on_Unit_goto_B_X22__payload_skip: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_Init_on_Unit_goto_B_X22__payload_skip := actual_B_Init_on_Unit_goto_B_X22__payload_skip;
    assume {:sourceloc "", 22, 3} true;
    return;
}



procedure B_X_on_F_goto_B_X31(actual_B_X_on_F_goto_B_X31__payload_4: PrtRef);



implementation B_X_on_F_goto_B_X31(actual_B_X_on_F_goto_B_X31__payload_4: PrtRef)
{
  var B_X_on_F_goto_B_X31__payload_4: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_X_on_F_goto_B_X31__payload_4 := actual_B_X_on_F_goto_B_X31__payload_4;
    assume {:sourceloc "", 31, 22} true;
    assert PrtFieldBool(PrtFalse);
    return;
}



procedure B_Init_entry20(actual_B_Init_entry20__payload_1: PrtRef);
  modifies eventRaised, raisedEvent, raisedEventPl;



implementation B_Init_entry20(actual_B_Init_entry20__payload_1: PrtRef)
{
  var B_Init_entry20__payload_1: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_Init_entry20__payload_1 := actual_B_Init_entry20__payload_1;
    assume {:sourceloc "", 20, 4} true;
    eventRaised := true;
    raisedEvent := 2;
    raisedEventPl := null;
    return;
}



procedure B_Init_exit20(actual_B_Init_exit20__payload_skip: PrtRef);



implementation B_Init_exit20(actual_B_Init_exit20__payload_skip: PrtRef)
{
  var B_Init_exit20__payload_skip: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_Init_exit20__payload_skip := actual_B_Init_exit20__payload_skip;
    assume {:sourceloc "", 20, 4} true;
    return;
}



procedure B_X_entry27_case_E123(actual_B_X_entry27_case_E123__payload_3: PrtRef, actual_B_X_entry27_case_E123_env: PrtRef) returns (ret: PrtRef);
  modifies tmpRhsValue_0;



implementation B_X_entry27_case_E123(actual_B_X_entry27_case_E123__payload_3: PrtRef, actual_B_X_entry27_case_E123_env: PrtRef) returns (ret: PrtRef)
{
  var B_X_entry27_case_E123__payload_3: PrtRef;
  var B_X_entry27_case_E123_env: PrtRef;
  var B_X_entry27__payload_2: PrtRef;
  var Tmp133: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_X_entry27_case_E123__payload_3 := actual_B_X_entry27_case_E123__payload_3;
    B_X_entry27_case_E123_env := actual_B_X_entry27_case_E123_env;
    B_X_entry27__payload_2 := null;
    B_X_entry27__payload_2 := PrtFieldTuple0(B_X_entry27_case_E123_env);
    assume {:sourceloc "", 28, 15} true;
    tmpRhsValue_0 := B_X_entry27__payload_2;
    call {:si_unique_call 15} Tmp133 := AllocatePrtRef();
    assume PrtDynamicType(Tmp133) == PrtTypeTuple1;
    assume PrtFieldTuple0(Tmp133) == tmpRhsValue_0;
    ret := Tmp133;
    return;
}



procedure {:yields} B_X_entry27(actual_B_X_entry27__payload_2: PrtRef);
  modifies tmpRhsValue_0, eventRaised, machineEvToQCount, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



implementation B_X_entry27(actual_B_X_entry27__payload_2: PrtRef)
{
  var B_X_entry27__payload_2: PrtRef;
  var B_X_entry27_case_E123_env: PrtRef;
  var Tmp134: PrtRef;
  var Tmp135: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_X_entry27__payload_2 := actual_B_X_entry27__payload_2;
    Tmp135 := null;
    tmpRhsValue_0 := Tmp135;
    call {:si_unique_call 16} Tmp134 := AllocatePrtRef();
    assume PrtDynamicType(Tmp134) == PrtTypeTuple1;
    assume PrtFieldTuple0(Tmp134) == tmpRhsValue_0;
    B_X_entry27_case_E123_env := Tmp134;
    assume {:sourceloc "", 27, 4} true;
    yield;
    call {:si_unique_call 17} event, payload := Dequeue();
    goto anon4_Then, anon4_Else;

  anon4_Then:
    assume {:partition} event == 0;
    tmpRhsValue_0 := B_X_entry27__payload_2;
    call {:si_unique_call 18} B_X_entry27_case_E123_env := AllocatePrtRef();
    assume PrtDynamicType(B_X_entry27_case_E123_env) == PrtTypeTuple1;
    assume PrtFieldTuple0(B_X_entry27_case_E123_env) == tmpRhsValue_0;
    call {:si_unique_call 19} B_X_entry27_case_E123_env := B_X_entry27_case_E123(payload, B_X_entry27_case_E123_env);
    B_X_entry27__payload_2 := PrtFieldTuple0(B_X_entry27_case_E123_env);
    goto anon3;

  anon4_Else:
    assume {:partition} event != 0;
    assert false;
    goto anon3;

  anon3:
    return;
}



procedure B_X_exit27(actual_B_X_exit27__payload_skip: PrtRef);



implementation B_X_exit27(actual_B_X_exit27__payload_skip: PrtRef)
{
  var B_X_exit27__payload_skip: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    B_X_exit27__payload_skip := actual_B_X_exit27__payload_skip;
    assume {:sourceloc "", 27, 4} true;
    return;
}



procedure B_ProbeStateStack(event: int);
  modifies CurrState, StateStack;



implementation B_ProbeStateStack(event: int)
{

  anon0:
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} registerEvents[CurrState][event];
    return;

  anon6_Else:
    assume {:partition} !registerEvents[CurrState][event];
    goto anon2;

  anon2:
    goto anon7_LoopHead;

  anon7_LoopHead:
    goto anon7_LoopDone, anon7_LoopBody;

  anon7_LoopBody:
    assume {:partition} StateStack != Nil();
    call {:si_unique_call 20} B_CallExitAction();
    CurrState := state#Cons(StateStack);
    StateStack := stack#Cons(StateStack);
    goto anon8_Then, anon8_Else;

  anon8_Then:
    assume {:partition} registerEvents[CurrState][event];
    return;

  anon8_Else:
    assume {:partition} !registerEvents[CurrState][event];
    goto anon7_LoopHead;

  anon7_LoopDone:
    assume {:partition} StateStack == Nil();
    goto anon5;

  anon5:
    return;
}



procedure {:yields} B_CallEntryAction(state: int, payload: PrtRef);
  modifies eventRaised, raisedEvent, raisedEventPl, tmpRhsValue_0, machineEvToQCount, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



implementation B_CallEntryAction(state: int, payload: PrtRef)
{

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Then:
    assume {:partition} state == 0;
    call {:si_unique_call 21} B_Init_entry20(payload);
    goto anon2;

  anon4_Else:
    assume {:partition} state != 0;
    goto anon2;

  anon2:
    goto anon5_Then, anon5_Else;

  anon5_Then:
    assume {:partition} state == 1;
    call {:si_unique_call 22} B_X_entry27(payload);
    return;

  anon5_Else:
    assume {:partition} state != 1;
    return;
}



procedure B_CallExitAction();



implementation B_CallExitAction()
{

  anon0:
    goto anon4_Then, anon4_Else;

  anon4_Then:
    assume {:partition} CurrState == 0;
    call {:si_unique_call 23} B_Init_exit20(null);
    goto anon2;

  anon4_Else:
    assume {:partition} CurrState != 0;
    goto anon2;

  anon2:
    goto anon5_Then, anon5_Else;

  anon5_Then:
    assume {:partition} CurrState == 1;
    call {:si_unique_call 24} B_X_exit27(null);
    return;

  anon5_Else:
    assume {:partition} CurrState != 1;
    return;
}



procedure {:yields} MachineThread_B(mid: int, entryArg: PrtRef);
  modifies StateStack, CurrState, eventRaised, thisMid, registerEvents, raisedEvent, raisedEventPl, machineEvToQCount, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent, tmpRhsValue_0;



implementation MachineThread_B(mid: int, entryArg: PrtRef)
{
  var event: int;
  var payload: PrtRef;
  var depth: int;

  anon0:
    StateStack := Nil();
    CurrState := 0;
    eventRaised := false;
    thisMid := mid;
    registerEvents[0][0] := false;
    registerEvents[0][1] := false;
    registerEvents[0][2] := true;
    registerEvents[0][3] := false;
    registerEvents[0][4] := false;
    registerEvents[1][0] := false;
    registerEvents[1][1] := true;
    registerEvents[1][2] := false;
    registerEvents[1][3] := false;
    registerEvents[1][4] := false;
    call {:si_unique_call 25} B_Init_entry20(entryArg);
    goto anon9_LoopHead;

  anon9_LoopHead:
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} true;
    yield;
    call {:si_unique_call 26} event, payload := Dequeue();
    call {:si_unique_call 27} B_ProbeStateStack(event);
    goto anon10_Then, anon10_Else;

  anon10_Then:
    assume {:partition} CurrState == 0;
    goto B_Init;

  B_Init:
    goto anon11_Then, anon11_Else;

  anon11_Then:
    assume {:partition} event == 2;
    call {:si_unique_call 28} B_CallExitAction();
    call {:si_unique_call 29} B_Init_on_Unit_goto_B_X22(payload);
    CurrState := 1;
    call {:si_unique_call 30} B_CallEntryAction(1, payload);
    goto anon9_LoopHead;

  anon11_Else:
    assume {:partition} event != 2;
    goto anon12_Then, anon12_Else;

  anon12_Then:
    assume {:partition} event == 3;
    return;

  anon12_Else:
    assume {:partition} event != 3;
    assert false;
    goto anon9_LoopHead;

  anon10_Else:
    assume {:partition} CurrState != 0;
    goto anon13_Then, anon13_Else;

  anon13_Then:
    assume {:partition} CurrState == 1;
    goto B_X;

  B_X:
    goto anon14_Then, anon14_Else;

  anon14_Then:
    assume {:partition} event == 1;
    call {:si_unique_call 31} B_CallExitAction();
    call {:si_unique_call 32} B_X_on_F_goto_B_X31(payload);
    CurrState := 1;
    call {:si_unique_call 33} B_CallEntryAction(1, payload);
    goto anon9_LoopHead;

  anon14_Else:
    assume {:partition} event != 1;
    goto anon15_Then, anon15_Else;

  anon15_Then:
    assume {:partition} event == 3;
    return;

  anon15_Else:
    assume {:partition} event != 3;
    assert false;
    goto anon9_LoopHead;

  anon13_Else:
    assume {:partition} CurrState != 1;
    assume false;
    goto anon9_LoopHead;

  anon9_LoopDone:
    assume {:partition} !true;
    return;
}



procedure {:yields} {:entrypoint} main();
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, StateStack, CurrState, eventRaised, thisMid, Main_x, registerEvents, MachineInboxTail, MachineInboxStoreEvent, MachineInboxStorePayload, MachineInboxHead, raisedEvent, raisedEventPl, tmpRhsValue_0;



implementation {:entrypoint} main()
{
  var tmpRhsValue: PrtRef;

  anon0:
    machineCounter := 0;
    yield;
    call {:si_unique_call 34} tmpRhsValue := newMachine_Main(null);
    return;
}






