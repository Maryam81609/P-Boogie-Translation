type PrtType;

const unique PrtTypeNull: PrtType;

const unique PrtTypeInt: PrtType;

const unique PrtTypeBool: PrtType;

const unique PrtTypeMachine: PrtType;

const unique PrtTypeEvent: PrtType;

const unique PrtTypeTuple1: PrtType;

const unique PrtTypeTuple2: PrtType;

const unique PrtTypeSeq3: PrtType;

const unique PrtTypeMap4: PrtType;

const unique PrtTypeMap5: PrtType;

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

function PrtFieldTuple1(PrtRef) : PrtRef;

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

var {:thread_local} Main_j: PrtRef;

var {:thread_local} Main_i: PrtRef;

var {:thread_local} Main_s1: PrtRef;

var {:thread_local} Main_s: PrtRef;

var {:thread_local} Main_t1: PrtRef;

var {:thread_local} Main_t: PrtRef;

var {:thread_local} Main_ts: PrtRef;

var {:thread_local} Main_m: PrtRef;

var {:thread_local} Tmp358: PrtRef;

var {:thread_local} Tmp359: PrtRef;

var {:thread_local} Tmp360: PrtRef;

var {:thread_local} Tmp361: PrtRef;

var {:thread_local} Tmp362: PrtRef;

var {:thread_local} Tmp363: PrtRef;

var {:thread_local} Tmp364: PrtRef;

var {:thread_local} Tmp365: PrtRef;

var {:thread_local} Tmp366: PrtRef;

var {:thread_local} Tmp367: PrtRef;

var {:thread_local} Tmp368: PrtRef;

var {:thread_local} Tmp369: PrtRef;

var {:thread_local} Tmp370: PrtRef;

var {:thread_local} Tmp371: PrtRef;

var {:thread_local} Tmp372: PrtRef;

var {:thread_local} Tmp373: PrtRef;

var {:thread_local} Tmp374: PrtRef;

var {:thread_local} Tmp375: PrtRef;

var {:thread_local} Tmp376: PrtRef;

var {:thread_local} Tmp377: PrtRef;

var {:thread_local} registerEvents: [int][int]bool;

var {:thread_local} tmpRhsValue: PrtRef;

var {:thread_local} tmpRhsValue_0: PrtRef;

var {:thread_local} tmpRhsValue_1: PrtRef;

procedure monitor(event: int, payload: PrtRef);



procedure AssertPayloadDynamicType(event: PrtRef, payload: PrtRef) returns (evID: int);



procedure PrtEquals(a: PrtRef, b: PrtRef) returns (v: PrtRef);



implementation PrtEquals(a: PrtRef, b: PrtRef) returns (v: PrtRef)
{
  var ta: PrtType;
  var tb: PrtType;

  anon0:
    goto anon17_Then, anon17_Else;

  anon17_Then:
    assume {:partition} a == b;
    v := PrtTrue;
    return;

  anon17_Else:
    assume {:partition} a != b;
    goto anon2;

  anon2:
    ta := PrtDynamicType(a);
    tb := PrtDynamicType(b);
    goto anon18_Then, anon18_Else;

  anon18_Then:
    assume {:partition} ta != tb;
    v := PrtFalse;
    return;

  anon18_Else:
    assume {:partition} ta == tb;
    goto anon4;

  anon4:
    goto anon19_Then, anon19_Else;

  anon19_Then:
    assume {:partition} ta == PrtTypeInt;
    v := PrtConstructFromBool(PrtFieldInt(a) == PrtFieldInt(b));
    return;

  anon19_Else:
    assume {:partition} ta != PrtTypeInt;
    goto anon6;

  anon6:
    goto anon20_Then, anon20_Else;

  anon20_Then:
    assume {:partition} ta == PrtTypeBool;
    v := PrtConstructFromBool(PrtFieldBool(a) <==> PrtFieldBool(b));
    return;

  anon20_Else:
    assume {:partition} ta != PrtTypeBool;
    goto anon8;

  anon8:
    goto anon21_Then, anon21_Else;

  anon21_Then:
    assume {:partition} ta == PrtTypeMachine;
    v := PrtConstructFromBool(PrtFieldMachine(a) == PrtFieldMachine(b));
    return;

  anon21_Else:
    assume {:partition} ta != PrtTypeMachine;
    goto anon10;

  anon10:
    goto anon22_Then, anon22_Else;

  anon22_Then:
    assume {:partition} ta == PrtTypeEvent;
    v := PrtConstructFromBool(PrtFieldEvent(a) == PrtFieldEvent(b));
    return;

  anon22_Else:
    assume {:partition} ta != PrtTypeEvent;
    goto anon12;

  anon12:
    goto anon23_Then, anon23_Else;

  anon23_Then:
    assume {:partition} ta == PrtTypeTuple1;
    call {:si_unique_call 0} v := PrtEqualsTuple1(a, b);
    return;

  anon23_Else:
    assume {:partition} ta != PrtTypeTuple1;
    goto anon14;

  anon14:
    goto anon24_Then, anon24_Else;

  anon24_Then:
    assume {:partition} ta == PrtTypeTuple2;
    call {:si_unique_call 1} v := PrtEqualsTuple2(a, b);
    return;

  anon24_Else:
    assume {:partition} ta != PrtTypeTuple2;
    goto anon16;

  anon16:
    assume false;
    return;
}



procedure PrtEqualsTuple1(x: PrtRef, y: PrtRef) returns (v: PrtRef);



implementation PrtEqualsTuple1(x: PrtRef, y: PrtRef) returns (v: PrtRef)
{

  anon0:
    call {:si_unique_call 2} v := PrtEquals(PrtFieldTuple0(x), PrtFieldTuple0(y));
    return;
}



procedure PrtEqualsTuple2(x: PrtRef, y: PrtRef) returns (v: PrtRef);



implementation PrtEqualsTuple2(x: PrtRef, y: PrtRef) returns (v: PrtRef)
{

  anon0:
    call {:si_unique_call 3} v := PrtEquals(PrtFieldTuple0(x), PrtFieldTuple0(y));
    goto anon3_Then, anon3_Else;

  anon3_Then:
    assume {:partition} v == PrtFalse;
    return;

  anon3_Else:
    assume {:partition} v != PrtFalse;
    goto anon2;

  anon2:
    call {:si_unique_call 4} v := PrtEquals(PrtFieldTuple1(x), PrtFieldTuple1(y));
    return;
}



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



procedure WriteSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef);



implementation {:ForceInline} WriteSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef)
{
  var store: [int]PrtRef;
  var size: int;

  anon0:
    assert SeqIndexInBounds(seq, index);
    size := PrtFieldSeqSize(seq);
    store := PrtFieldSeqStore(seq);
    store[index] := value;
    call {:si_unique_call 5} nseq := AllocatePrtRef();
    assume PrtDynamicType(nseq) == PrtDynamicType(seq);
    assume PrtFieldSeqSize(nseq) == size;
    assume PrtFieldSeqStore(nseq) == store;
    return;
}



procedure RemoveSeq(seq: PrtRef, index: int) returns (nseq: PrtRef);



implementation {:ForceInline} RemoveSeq(seq: PrtRef, index: int) returns (nseq: PrtRef)
{
  var oldStore: [int]PrtRef;
  var newStore: [int]PrtRef;
  var size: int;
  var i: int;

  anon0:
    size := PrtFieldSeqSize(seq);
    i := 0;
    oldStore := PrtFieldSeqStore(seq);
    assert SeqIndexInBounds(seq, index);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < index;
    newStore[i] := oldStore[i];
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} index <= i;
    goto anon2;

  anon2:
    goto anon6_LoopHead;

  anon6_LoopHead:
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    assume {:partition} i < size - 1;
    newStore[i] := oldStore[i + 1];
    i := i + 1;
    goto anon6_LoopHead;

  anon6_LoopDone:
    assume {:partition} size - 1 <= i;
    goto anon4;

  anon4:
    call {:si_unique_call 6} nseq := AllocatePrtRef();
    assume PrtDynamicType(nseq) == PrtDynamicType(seq);
    assume PrtFieldSeqSize(nseq) == size - 1;
    assume PrtFieldSeqStore(nseq) == newStore;
    return;
}



procedure InsertSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef);



implementation {:ForceInline} InsertSeq(seq: PrtRef, index: int, value: PrtRef) returns (nseq: PrtRef)
{
  var oldStore: [int]PrtRef;
  var newStore: [int]PrtRef;
  var size: int;
  var i: int;

  anon0:
    size := PrtFieldSeqSize(seq);
    i := 0;
    assert 0 <= index && index <= size;
    oldStore := PrtFieldSeqStore(seq);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < index;
    newStore[i] := oldStore[i];
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} index <= i;
    goto anon2;

  anon2:
    newStore[index] := value;
    i := i + 1;
    goto anon6_LoopHead;

  anon6_LoopHead:
    goto anon6_LoopDone, anon6_LoopBody;

  anon6_LoopBody:
    assume {:partition} i < size;
    newStore[i + 1] := oldStore[i];
    i := i + 1;
    goto anon6_LoopHead;

  anon6_LoopDone:
    assume {:partition} size <= i;
    goto anon4;

  anon4:
    call {:si_unique_call 7} nseq := AllocatePrtRef();
    assume PrtFieldSeqSize(nseq) == size + 1;
    assume PrtFieldSeqStore(nseq) == newStore;
    assume PrtDynamicType(nseq) == PrtDynamicType(seq);
    return;
}



procedure MapContainsKey(map: PrtRef, key: PrtRef) returns (v: bool);



implementation {:ForceInline} MapContainsKey(map: PrtRef, key: PrtRef) returns (v: bool)
{
  var size: int;
  var i: int;
  var keys: [int]PrtRef;

  anon0:
    v := false;
    size := PrtFieldMapSize(map);
    i := 0;
    keys := PrtFieldMapKeys(map);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < size;
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} keys[i] == key;
    v := true;
    return;

  anon6_Else:
    assume {:partition} keys[i] != key;
    goto anon3;

  anon3:
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} size <= i;
    goto anon4;

  anon4:
    return;
}



procedure ReadMap(map: PrtRef, key: PrtRef) returns (value: PrtRef);



implementation {:ForceInline} ReadMap(map: PrtRef, key: PrtRef) returns (value: PrtRef)
{
  var size: int;
  var i: int;
  var keys: [int]PrtRef;
  var values: [int]PrtRef;

  anon0:
    size := PrtFieldMapSize(map);
    i := 0;
    keys := PrtFieldMapKeys(map);
    values := PrtFieldMapValues(map);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < size;
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} keys[i] == key;
    value := values[i];
    return;

  anon6_Else:
    assume {:partition} keys[i] != key;
    goto anon3;

  anon3:
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} size <= i;
    goto anon4;

  anon4:
    assert false;
    return;
}



procedure MapGetKeys(map: PrtRef) returns (seq: PrtRef);



implementation {:ForceInline} MapGetKeys(map: PrtRef) returns (seq: PrtRef)
{
  var size: int;
  var store: [int]PrtRef;

  anon0:
    store := PrtFieldMapKeys(map);
    size := PrtFieldMapSize(map);
    call {:si_unique_call 8} seq := AllocatePrtRef();
    assume PrtFieldSeqStore(seq) == store;
    assume PrtFieldSeqSize(seq) == size;
    return;
}



procedure MapGetValues(map: PrtRef) returns (seq: PrtRef);



procedure WriteMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef);



implementation {:ForceInline} WriteMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef)
{
  var size: int;
  var i: int;
  var flag: bool;
  var keys: [int]PrtRef;
  var values: [int]PrtRef;

  anon0:
    size := PrtFieldMapSize(map);
    i := 0;
    keys := PrtFieldMapKeys(map);
    values := PrtFieldMapValues(map);
    flag := false;
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < size;
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} keys[i] == key;
    values[i] := value;
    flag := true;
    goto anon3;

  anon6_Else:
    assume {:partition} keys[i] != key;
    goto anon3;

  anon3:
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} size <= i;
    goto anon4;

  anon4:
    assert flag;
    call {:si_unique_call 9} nmap := AllocatePrtRef();
    assume PrtDynamicType(nmap) == PrtDynamicType(map);
    assume PrtFieldMapSize(nmap) == size;
    assume PrtFieldMapKeys(nmap) == keys;
    assume PrtFieldMapValues(nmap) == values;
    return;
}



procedure InsertMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef);



implementation {:ForceInline} InsertMap(map: PrtRef, key: PrtRef, value: PrtRef) returns (nmap: PrtRef)
{
  var size: int;
  var i: int;
  var keys: [int]PrtRef;
  var values: [int]PrtRef;

  anon0:
    size := PrtFieldMapSize(map);
    i := 0;
    keys := PrtFieldMapKeys(map);
    values := PrtFieldMapValues(map);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} i < size;
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} keys[i] == key;
    assert false;
    goto anon3;

  anon6_Else:
    assume {:partition} keys[i] != key;
    goto anon3;

  anon3:
    i := i + 1;
    goto anon5_LoopHead;

  anon5_LoopDone:
    assume {:partition} size <= i;
    goto anon4;

  anon4:
    keys[size] := key;
    values[size] := value;
    call {:si_unique_call 10} nmap := AllocatePrtRef();
    assume PrtDynamicType(nmap) == PrtDynamicType(map);
    assume PrtFieldMapSize(nmap) == size + 1;
    assume PrtFieldMapKeys(nmap) == keys;
    assume PrtFieldMapValues(nmap) == values;
    return;
}



procedure RemoveMap(map: PrtRef, key: PrtRef) returns (nmap: PrtRef);



implementation {:ForceInline} RemoveMap(map: PrtRef, key: PrtRef) returns (nmap: PrtRef)
{
  var size: int;
  var i: int;
  var flag: bool;
  var oldKeys: [int]PrtRef;
  var oldValues: [int]PrtRef;
  var newKeys: [int]PrtRef;
  var newValues: [int]PrtRef;

  anon0:
    size := PrtFieldMapSize(map);
    assert size > 0;
    i := 0;
    oldKeys := PrtFieldMapKeys(map);
    oldValues := PrtFieldMapValues(map);
    flag := false;
    goto anon7_LoopHead;

  anon7_LoopHead:
    goto anon7_LoopDone, anon7_LoopBody;

  anon7_LoopBody:
    assume {:partition} i < size && oldKeys[i] != key;
    newKeys[i] := oldKeys[i];
    newValues[i] := oldValues[i];
    goto anon8_Then, anon8_Else;

  anon8_Then:
    assume {:partition} oldKeys[i] == key;
    flag := true;
    newKeys[i] := oldKeys[size - 1];
    newValues[i] := oldValues[size - 1];
    goto anon3;

  anon8_Else:
    assume {:partition} oldKeys[i] != key;
    goto anon3;

  anon3:
    i := i + 1;
    goto anon7_LoopHead;

  anon7_LoopDone:
    assume {:partition} !(i < size && oldKeys[i] != key);
    goto anon4;

  anon4:
    assert flag;
    goto anon9_LoopHead;

  anon9_LoopHead:
    goto anon9_LoopDone, anon9_LoopBody;

  anon9_LoopBody:
    assume {:partition} i < size - 1;
    newKeys[i] := oldKeys[i + 1];
    newValues[i] := oldValues[i + 1];
    i := i + 1;
    goto anon9_LoopHead;

  anon9_LoopDone:
    assume {:partition} size - 1 <= i;
    goto anon6;

  anon6:
    call {:si_unique_call 11} nmap := AllocatePrtRef();
    assume PrtDynamicType(nmap) == PrtDynamicType(map);
    assume PrtFieldMapSize(nmap) == size - 1;
    assume PrtFieldMapKeys(nmap) == newKeys;
    assume PrtFieldMapValues(nmap) == newValues;
    return;
}



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



procedure Enqueue(mid: int, event: int, payload: PrtRef);



procedure send(mid: int, event: int, payload: PrtRef);



procedure {:yields} newMachine_Main(entryArg: PrtRef) returns (m: PrtRef);
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, StateStack, CurrState, eventRaised, thisMid, Tmp361, tmpRhsValue_0, Tmp360, Tmp359, Tmp358, Main_x, Main_j, Main_i, Tmp362, Main_s1, Tmp363, Main_s, Tmp366, Tmp365, Tmp368, Tmp367, tmpRhsValue_1, Tmp364, Main_t1, Tmp371, Tmp370, Tmp373, Tmp372, Tmp369, Main_t, Tmp375, Tmp376, Tmp374, Main_ts, Tmp377, Main_m, registerEvents, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



implementation newMachine_Main(entryArg: PrtRef) returns (m: PrtRef)
{
  var tmp: int;

  anon0:
    machineCounter := machineCounter + 1;
    tmp := machineCounter;
    call {:si_unique_call 12} InitializeInbox(tmp);
    machineToQCAssert[tmp] := 0 - 1;
    machineToQCAssume[tmp] := 0 - 1;
    machineEvToQCount[tmp][0] := 0;
    machineEvToQCount[tmp][1] := 0;
    yield;
    async call {:si_unique_call 13} MachineThread_Main(tmp, entryArg);
    m := PrtConstructFromMachineId(tmp);
    return;
}



procedure Main_F() returns (ret: PrtRef);



implementation Main_F() returns (ret: PrtRef)
{
  var Tmp378: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    assume {:sourceloc "", 9, 6} true;
    havoc Tmp378;
    goto anon3_Then, anon3_Else;

  anon3_Then:
    assume {:partition} PrtFieldBool(Tmp378);
    assume {:sourceloc "", 10, 7} true;
    ret := PrtConstructFromInt(0);
    return;

  anon3_Else:
    assume {:partition} !PrtFieldBool(Tmp378);
    assume {:sourceloc "", 12, 7} true;
    ret := PrtConstructFromInt(1);
    return;
}



procedure Main_foo() returns (ret: PrtRef);



implementation Main_foo() returns (ret: PrtRef)
{
  var event: int;
  var payload: PrtRef;

  anon0:
    assume {:sourceloc "", 18, 8} true;
    ret := PrtConstructFromInt(1);
    return;
}



procedure Main_S_entry36(actual_Main_S_entry36__payload_0: PrtRef);
  modifies Main_i, tmpRhsValue_0, Main_x, tmpRhsValue_1, Main_ts, Main_t, Main_s, Main_s1, Main_m, Main_j;



implementation Main_S_entry36(actual_Main_S_entry36__payload_0: PrtRef)
{
  var Main_S_entry36__payload_0: PrtRef;
  var Tmp379: PrtRef;
  var Tmp380: PrtRef;
  var Tmp381: PrtRef;
  var Tmp382: PrtRef;
  var Tmp383: PrtRef;
  var Tmp384: PrtRef;
  var Tmp385: PrtRef;
  var Tmp386: PrtRef;
  var Tmp387: PrtRef;
  var Tmp388: PrtRef;
  var Tmp389: PrtRef;
  var Tmp390: PrtRef;
  var Tmp391: PrtRef;
  var Tmp392: PrtRef;
  var Tmp393: PrtRef;
  var Tmp394: PrtRef;
  var Tmp395: PrtRef;
  var Tmp396: PrtRef;
  var Tmp397: PrtRef;
  var Tmp398: PrtRef;
  var Tmp399: PrtRef;
  var Tmp400: PrtRef;
  var Tmp401: PrtRef;
  var Tmp402: PrtRef;
  var Tmp403: PrtRef;
  var Tmp404: PrtRef;
  var Tmp405: PrtRef;
  var Tmp406: PrtRef;
  var Tmp407: PrtRef;
  var Tmp408: PrtRef;
  var Tmp409: PrtRef;
  var Tmp410: PrtRef;
  var Tmp411: PrtRef;
  var Tmp412: PrtRef;
  var Tmp413: PrtRef;
  var Tmp414: PrtRef;
  var Tmp415: PrtRef;
  var Tmp416: PrtRef;
  var Tmp417: PrtRef;
  var Tmp418: PrtRef;
  var Tmp419: PrtRef;
  var Tmp420: PrtRef;
  var Tmp421: PrtRef;
  var Tmp422: PrtRef;
  var Tmp423: PrtRef;
  var Tmp424: PrtRef;
  var Tmp425: PrtRef;
  var Tmp426: PrtRef;
  var Tmp427: PrtRef;
  var Tmp428: PrtRef;
  var Tmp429: PrtRef;
  var Tmp430: PrtRef;
  var Tmp431: PrtRef;
  var Tmp432: PrtRef;
  var Tmp433: PrtRef;
  var Tmp434: PrtRef;
  var Tmp435: PrtRef;
  var Tmp436: PrtRef;
  var Tmp437: PrtRef;
  var Tmp438: PrtRef;
  var Tmp439: PrtRef;
  var Tmp440: PrtRef;
  var Tmp441: PrtRef;
  var Tmp442: PrtRef;
  var Tmp443: PrtRef;
  var Tmp444: PrtRef;
  var Tmp445: PrtRef;
  var Tmp446: PrtRef;
  var Tmp447: PrtRef;
  var Tmp448: PrtRef;
  var Tmp449: PrtRef;
  var Tmp450: PrtRef;
  var Tmp451: PrtRef;
  var Tmp452: PrtRef;
  var Tmp453: PrtRef;
  var Tmp454: PrtRef;
  var Tmp455: PrtRef;
  var Tmp456: PrtRef;
  var Tmp457: PrtRef;
  var Tmp458: PrtRef;
  var Tmp459: PrtRef;
  var Tmp460: PrtRef;
  var Tmp461: PrtRef;
  var Tmp462: PrtRef;
  var Tmp463: PrtRef;
  var Tmp464: PrtRef;
  var Tmp465: PrtRef;
  var Tmp466: PrtRef;
  var Tmp467: PrtRef;
  var Tmp468: PrtRef;
  var Tmp469: PrtRef;
  var Tmp470: PrtRef;
  var Tmp471: PrtRef;
  var Tmp472: PrtRef;
  var Tmp473: PrtRef;
  var Tmp474: PrtRef;
  var Tmp475: PrtRef;
  var Tmp476: PrtRef;
  var Tmp477: PrtRef;
  var Tmp478: PrtRef;
  var Tmp479: PrtRef;
  var Tmp480: PrtRef;
  var Tmp481: PrtRef;
  var Tmp482: PrtRef;
  var Tmp483: PrtRef;
  var Tmp484: PrtRef;
  var Tmp485: PrtRef;
  var Tmp486: PrtRef;
  var Tmp487: PrtRef;
  var Tmp488: PrtRef;
  var Tmp489: PrtRef;
  var Tmp490: PrtRef;
  var Tmp491: PrtRef;
  var Tmp492: PrtRef;
  var Tmp493: PrtRef;
  var Tmp494: PrtRef;
  var Tmp495: PrtRef;
  var Tmp496: PrtRef;
  var Tmp497: PrtRef;
  var Tmp498: PrtRef;
  var Tmp499: PrtRef;
  var Tmp500: PrtRef;
  var Tmp501: PrtRef;
  var Tmp502: PrtRef;
  var Tmp503: PrtRef;
  var Tmp504: PrtRef;
  var Tmp505: PrtRef;
  var Tmp506: PrtRef;
  var Tmp507: PrtRef;
  var Tmp508: PrtRef;
  var Tmp509: PrtRef;
  var Tmp510: PrtRef;
  var Tmp511: PrtRef;
  var Tmp512: PrtRef;
  var Tmp513: PrtRef;
  var Tmp514: PrtRef;
  var Tmp515: PrtRef;
  var Tmp516: PrtRef;
  var Tmp517: PrtRef;
  var Tmp518: PrtRef;
  var Tmp519: PrtRef;
  var Tmp520: PrtRef;
  var Tmp521: PrtRef;
  var Tmp522: PrtRef;
  var Tmp523: PrtRef;
  var Tmp524: PrtRef;
  var Tmp525: PrtRef;
  var Tmp526: PrtRef;
  var Tmp527: PrtRef;
  var Tmp528: PrtRef;
  var Tmp529: PrtRef;
  var Tmp530: PrtRef;
  var Tmp531: PrtRef;
  var Tmp532: PrtRef;
  var Tmp533: PrtRef;
  var Tmp534: PrtRef;
  var Tmp535: PrtRef;
  var Tmp536: PrtRef;
  var Tmp537: PrtRef;
  var Tmp538: PrtRef;
  var Tmp539: PrtRef;
  var Tmp540: PrtRef;
  var Tmp541: PrtRef;
  var Tmp542: PrtRef;
  var Tmp543: PrtRef;
  var Tmp544: PrtRef;
  var Tmp545: PrtRef;
  var Tmp546: PrtRef;
  var Tmp547: PrtRef;
  var Tmp548: PrtRef;
  var Tmp549: PrtRef;
  var Tmp550: PrtRef;
  var Tmp551: PrtRef;
  var Tmp552: PrtRef;
  var Tmp553: PrtRef;
  var Tmp554: PrtRef;
  var Tmp555: PrtRef;
  var Tmp556: PrtRef;
  var Tmp557: PrtRef;
  var Tmp558: PrtRef;
  var Tmp559: PrtRef;
  var Tmp560: PrtRef;
  var Tmp561: PrtRef;
  var Tmp562: PrtRef;
  var Tmp563: PrtRef;
  var Tmp564: PrtRef;
  var Tmp565: PrtRef;
  var Tmp566: PrtRef;
  var Tmp567: PrtRef;
  var Tmp568: PrtRef;
  var Tmp569: PrtRef;
  var Tmp570: PrtRef;
  var Tmp571: PrtRef;
  var Tmp572: PrtRef;
  var Tmp573: PrtRef;
  var Tmp574: PrtRef;
  var Tmp575: PrtRef;
  var Tmp576: PrtRef;
  var Tmp577: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    Main_S_entry36__payload_0 := actual_Main_S_entry36__payload_0;
    assume {:sourceloc "", 36, 7} true;
    call {:si_unique_call 14} Main_i := Main_F();
    assume {:sourceloc "", 37, 4} true;
    tmpRhsValue_0 := Main_i;
    call {:si_unique_call 15} Tmp379 := AllocatePrtRef();
    assume PrtDynamicType(Tmp379) == PrtTypeTuple1;
    assume PrtFieldTuple0(Tmp379) == tmpRhsValue_0;
    tmpRhsValue_0 := Tmp379;
    call {:si_unique_call 16} Main_x := AllocatePrtRef();
    assume PrtDynamicType(Main_x) == PrtTypeTuple1;
    assume PrtFieldTuple0(Main_x) == tmpRhsValue_0;
    assume {:sourceloc "", 38, 4} true;
    call {:si_unique_call 17} Tmp380 := PrtEquals(PrtFieldTuple0(PrtFieldTuple0(Main_x)), PrtConstructFromInt(0));
    call {:si_unique_call 18} Tmp381 := PrtEquals(PrtFieldTuple0(PrtFieldTuple0(Main_x)), PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp381) || PrtFieldBool(Tmp381)));
    assume {:sourceloc "", 41, 4} true;
    tmpRhsValue_0 := Main_i;
    tmpRhsValue_1 := PrtFieldTuple1(Main_ts);
    call {:si_unique_call 19} Main_ts := AllocatePrtRef();
    assume PrtDynamicType(Main_ts) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_ts) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_ts) == tmpRhsValue_1;
    assume {:sourceloc "", 42, 4} true;
    call {:si_unique_call 20} Tmp382 := PrtEquals(PrtFieldTuple0(Main_ts), PrtConstructFromInt(0));
    call {:si_unique_call 21} Tmp383 := PrtEquals(PrtFieldTuple0(Main_ts), PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp383) || PrtFieldBool(Tmp383)));
    assume {:sourceloc "", 46, 4} true;
    tmpRhsValue_0 := Main_i;
    tmpRhsValue_1 := PrtFieldTuple1(Main_ts);
    call {:si_unique_call 22} Main_ts := AllocatePrtRef();
    assume PrtDynamicType(Main_ts) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_ts) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_ts) == tmpRhsValue_1;
    assume {:sourceloc "", 47, 4} true;
    call {:si_unique_call 23} Tmp384 := PrtEquals(PrtFieldTuple0(Main_ts), PrtConstructFromInt(0));
    call {:si_unique_call 24} Tmp385 := PrtEquals(PrtFieldTuple0(Main_ts), PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp385) || PrtFieldBool(Tmp385)));
    assume {:sourceloc "", 50, 4} true;
    Tmp386 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 25} Tmp386 := InsertSeq(Tmp386, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(2));
    tmpRhsValue_0 := Tmp386;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 26} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 51, 4} true;
    Tmp387 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 27} Tmp387 := InsertSeq(Tmp387, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(2));
    tmpRhsValue_0 := Tmp387;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 28} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 52, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp388 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 29} Tmp389 := PrtEquals(Tmp388, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp390 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 30} Tmp391 := PrtEquals(Tmp390, PrtConstructFromInt(2));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp391) && PrtFieldBool(Tmp391)));
    assume {:sourceloc "", 55, 4} true;
    call {:si_unique_call 31} Tmp392 := Main_foo();
    Tmp393 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 32} Tmp393 := WriteSeq(Tmp393, PrtFieldInt(Tmp392), PrtConstructFromInt(PrtFieldInt(Main_i) + PrtFieldInt(PrtConstructFromInt(5))));
    tmpRhsValue_0 := Tmp393;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 33} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 56, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp394 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 34} Tmp395 := PrtEquals(Tmp394, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp396 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 35} Tmp397 := PrtEquals(Tmp396, PrtConstructFromInt(5));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp398 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 36} Tmp399 := PrtEquals(Tmp398, PrtConstructFromInt(6));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp399) || PrtFieldBool(Tmp399))) && PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp399) || PrtFieldBool(Tmp399)))));
    assume {:sourceloc "", 57, 4} true;
    call {:si_unique_call 37} Tmp400 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(PrtFieldTuple0(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp400);
    assume {:sourceloc "", 61, 4} true;
    Tmp401 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 38} Tmp401 := InsertSeq(Tmp401, PrtFieldInt(PrtConstructFromInt(1)), Main_i);
    tmpRhsValue_0 := Tmp401;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 39} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 62, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp402 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 40} Tmp403 := PrtEquals(Tmp402, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp404 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 41} Tmp405 := PrtEquals(Tmp404, PrtConstructFromInt(0));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp406 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 42} Tmp407 := PrtEquals(Tmp406, PrtConstructFromInt(1));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(2)));
    Tmp408 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(2)));
    call {:si_unique_call 43} Tmp409 := PrtEquals(Tmp408, PrtConstructFromInt(5));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(2)));
    Tmp410 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(2)));
    call {:si_unique_call 44} Tmp411 := PrtEquals(Tmp410, PrtConstructFromInt(6));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp411) || PrtFieldBool(Tmp411))) && PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp411) || PrtFieldBool(Tmp411)))));
    assume {:sourceloc "", 65, 4} true;
    call {:si_unique_call 45} Tmp412 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(PrtFieldTuple0(Main_t))), PrtConstructFromInt(3));
    assert PrtFieldBool(Tmp412);
    assume {:sourceloc "", 77, 4} true;
    Tmp413 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 46} Tmp413 := RemoveSeq(Tmp413, PrtFieldInt(Main_i));
    tmpRhsValue_0 := Tmp413;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 47} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 78, 4} true;
    call {:si_unique_call 48} Tmp414 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(PrtFieldTuple0(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp414);
    assume {:sourceloc "", 79, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp415 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 49} Tmp416 := PrtEquals(Tmp415, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp417 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 50} Tmp418 := PrtEquals(Tmp417, PrtConstructFromInt(0));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp419 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 51} Tmp420 := PrtEquals(Tmp419, PrtConstructFromInt(1));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp421 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 52} Tmp422 := PrtEquals(Tmp421, PrtConstructFromInt(5));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp423 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 53} Tmp424 := PrtEquals(Tmp423, PrtConstructFromInt(6));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp424) || PrtFieldBool(Tmp424))) && PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp424) || PrtFieldBool(Tmp424)))));
    assume {:sourceloc "", 82, 4} true;
    call {:si_unique_call 54} Tmp425 := Main_foo();
    Tmp426 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 55} Tmp426 := RemoveSeq(Tmp426, PrtFieldInt(Tmp425));
    tmpRhsValue_0 := Tmp426;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 56} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 83, 4} true;
    call {:si_unique_call 57} Tmp427 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(PrtFieldTuple0(Main_t))), PrtConstructFromInt(1));
    assert PrtFieldBool(Tmp427);
    assume {:sourceloc "", 84, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp428 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 58} Tmp429 := PrtEquals(Tmp428, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp430 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 59} Tmp431 := PrtEquals(Tmp430, PrtConstructFromInt(0));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp432 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 60} Tmp433 := PrtEquals(Tmp432, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp433) || PrtFieldBool(Tmp433)));
    assume {:sourceloc "", 87, 4} true;
    Tmp434 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 61} Tmp434 := InsertSeq(Tmp434, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(2));
    tmpRhsValue_0 := Tmp434;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 62} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 88, 4} true;
    Tmp435 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 63} Tmp435 := InsertSeq(Tmp435, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(4));
    tmpRhsValue_0 := Tmp435;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 64} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 90, 4} true;
    Tmp436 := PrtFieldTuple0(Main_t);
    call {:si_unique_call 65} Tmp436 := WriteSeq(Tmp436, PrtFieldInt(Main_i), PrtConstructFromInt(5));
    tmpRhsValue_0 := Tmp436;
    tmpRhsValue_1 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 66} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 91, 4} true;
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp437 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 67} Tmp438 := PrtEquals(Tmp437, PrtConstructFromInt(2));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    Tmp439 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 68} Tmp440 := PrtEquals(Tmp439, PrtConstructFromInt(5));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp441 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 69} Tmp442 := PrtEquals(Tmp441, PrtConstructFromInt(4));
    assert SeqIndexInBounds(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    Tmp443 := ReadSeq(PrtFieldTuple0(Main_t), PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 70} Tmp444 := PrtEquals(Tmp443, PrtConstructFromInt(5));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp444) || PrtFieldBool(Tmp444))) && PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp444) || PrtFieldBool(Tmp444)))));
    assume {:sourceloc "", 94, 4} true;
    call {:si_unique_call 71} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(0));
    assume {:sourceloc "", 95, 4} true;
    call {:si_unique_call 72} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(1));
    assume {:sourceloc "", 96, 4} true;
    call {:si_unique_call 73} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(2));
    assume {:sourceloc "", 97, 4} true;
    call {:si_unique_call 74} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(3));
    assume {:sourceloc "", 98, 4} true;
    call {:si_unique_call 75} Tmp445 := AllocatePrtRef();
    assume PrtDynamicType(Tmp445) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp445) == 0;
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp445;
    call {:si_unique_call 76} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 99, 4} true;
    Tmp446 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 77} Tmp446 := InsertMap(Tmp446, PrtFieldInt(PrtConstructFromInt(0)), Main_s);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp446;
    call {:si_unique_call 78} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 100, 4} true;
    Tmp447 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 79} Tmp447 := InsertMap(Tmp447, PrtFieldInt(PrtConstructFromInt(1)), Main_s1);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp447;
    call {:si_unique_call 80} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 101, 4} true;
    call {:si_unique_call 81} Tmp448 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp448);
    assume {:sourceloc "", 102, 4} true;
    call {:si_unique_call 82} Tmp449 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    call {:si_unique_call 83} Tmp450 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(Tmp449)), PrtConstructFromInt(2));
    call {:si_unique_call 84} Tmp452 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp452, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp451 := ReadSeq(Tmp452, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 85} Tmp453 := PrtEquals(Tmp451, PrtConstructFromInt(0));
    call {:si_unique_call 86} Tmp455 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp455, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp454 := ReadSeq(Tmp455, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 87} Tmp456 := PrtEquals(Tmp454, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp456) && PrtFieldBool(Tmp456)));
    assume {:sourceloc "", 103, 4} true;
    call {:si_unique_call 88} Tmp457 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    call {:si_unique_call 89} Tmp458 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(Tmp457)), PrtConstructFromInt(2));
    call {:si_unique_call 90} Tmp460 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp460, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp459 := ReadSeq(Tmp460, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 91} Tmp461 := PrtEquals(Tmp459, PrtConstructFromInt(2));
    call {:si_unique_call 92} Tmp463 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp463, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp462 := ReadSeq(Tmp463, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 93} Tmp464 := PrtEquals(Tmp462, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp464) && PrtFieldBool(Tmp464)));
    assume {:sourceloc "", 107, 4} true;
    call {:si_unique_call 94} Main_m := InsertMap(Main_m, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(1));
    assume {:sourceloc "", 108, 4} true;
    call {:si_unique_call 95} Main_m := InsertMap(Main_m, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(2));
    assume {:sourceloc "", 109, 4} true;
    call {:si_unique_call 96} Main_i := Main_F();
    assume {:sourceloc "", 111, 4} true;
    call {:si_unique_call 97} Main_m := InsertMap(Main_m, PrtFieldInt(PrtConstructFromInt(2)), Main_i);
    assume {:sourceloc "", 112, 4} true;
    call {:si_unique_call 98} Tmp465 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(Main_m)), PrtConstructFromInt(3));
    call {:si_unique_call 99} Tmp466 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 100} Tmp467 := PrtEquals(Tmp466, PrtConstructFromInt(0));
    call {:si_unique_call 101} Tmp468 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 102} Tmp469 := PrtEquals(Tmp468, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp469) || PrtFieldBool(Tmp469))) && PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp469) || PrtFieldBool(Tmp469)))));
    assume {:sourceloc "", 114, 4} true;
    call {:si_unique_call 103} Main_m := WriteMap(Main_m, PrtConstructFromInt(3), PrtConstructFromInt(5));
    assume {:sourceloc "", 116, 4} true;
    call {:si_unique_call 104} Main_m := WriteMap(Main_m, PrtConstructFromInt(2), PrtConstructFromInt(PrtFieldInt(Main_i) + PrtFieldInt(PrtConstructFromInt(2))));
    assume {:sourceloc "", 117, 4} true;
    call {:si_unique_call 105} Tmp470 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(Main_m)), PrtConstructFromInt(4));
    assert PrtFieldBool(Tmp470);
    assume {:sourceloc "", 118, 4} true;
    call {:si_unique_call 106} Tmp471 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 107} Tmp472 := PrtEquals(Tmp471, PrtConstructFromInt(0));
    call {:si_unique_call 108} Tmp473 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 109} Tmp474 := PrtEquals(Tmp473, PrtConstructFromInt(1));
    call {:si_unique_call 110} Tmp475 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 111} Tmp476 := PrtEquals(Tmp475, PrtConstructFromInt(2));
    call {:si_unique_call 112} Tmp477 := ReadMap(Main_m, PrtConstructFromInt(2));
    call {:si_unique_call 113} Tmp478 := PrtEquals(Tmp477, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp478) || PrtFieldBool(Tmp478)));
    assume {:sourceloc "", 120, 4} true;
    call {:si_unique_call 114} Tmp479 := AllocatePrtRef();
    assume PrtDynamicType(Tmp479) == PrtTypeMap4;
    assume PrtFieldMapSize(Tmp479) == 0;
    Main_m := Tmp479;
    assume {:sourceloc "", 122, 4} true;
    call {:si_unique_call 115} Main_i := Main_F();
    assume {:sourceloc "", 123, 4} true;
    call {:si_unique_call 116} Main_m := InsertMap(Main_m, PrtFieldInt(Main_i), PrtConstructFromInt(0));
    assume {:sourceloc "", 124, 4} true;
    call {:si_unique_call 117} Tmp480 := MapContainsKey(PrtConstructFromInt(0), Main_m);
    goto anon22_Then, anon22_Else;

  anon22_Then:
    assume {:partition} PrtFieldBool(Tmp480);
    assume {:sourceloc "", 124, 17} true;
    call {:si_unique_call 118} Tmp481 := ReadMap(Main_m, PrtConstructFromInt(0));
    call {:si_unique_call 119} Tmp482 := PrtEquals(Tmp481, PrtConstructFromInt(0));
    assert PrtFieldBool(Tmp482);
    goto anon3;

  anon22_Else:
    assume {:partition} !PrtFieldBool(Tmp480);
    assume {:sourceloc "", 124, 4} true;
    goto anon3;

  anon3:
    assume {:sourceloc "", 125, 4} true;
    call {:si_unique_call 120} Tmp483 := MapContainsKey(PrtConstructFromInt(1), Main_m);
    goto anon23_Then, anon23_Else;

  anon23_Then:
    assume {:partition} PrtFieldBool(Tmp483);
    assume {:sourceloc "", 125, 17} true;
    call {:si_unique_call 121} Tmp484 := ReadMap(Main_m, PrtConstructFromInt(1));
    call {:si_unique_call 122} Tmp485 := PrtEquals(Tmp484, PrtConstructFromInt(0));
    assert PrtFieldBool(Tmp485);
    goto anon6;

  anon23_Else:
    assume {:partition} !PrtFieldBool(Tmp483);
    assume {:sourceloc "", 125, 4} true;
    goto anon6;

  anon6:
    assume {:sourceloc "", 127, 4} true;
    call {:si_unique_call 123} Tmp486 := AllocatePrtRef();
    assume PrtDynamicType(Tmp486) == PrtTypeMap4;
    assume PrtFieldMapSize(Tmp486) == 0;
    Main_m := Tmp486;
    assume {:sourceloc "", 128, 4} true;
    call {:si_unique_call 124} Main_m := WriteMap(Main_m, Main_i, PrtConstructFromInt(2));
    assume {:sourceloc "", 129, 4} true;
    call {:si_unique_call 125} Tmp487 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(Main_m)), PrtConstructFromInt(1));
    assert PrtFieldBool(Tmp487);
    assume {:sourceloc "", 130, 4} true;
    call {:si_unique_call 126} Tmp488 := MapContainsKey(PrtConstructFromInt(0), Main_m);
    goto anon24_Then, anon24_Else;

  anon24_Then:
    assume {:partition} PrtFieldBool(Tmp488);
    assume {:sourceloc "", 130, 17} true;
    call {:si_unique_call 127} Tmp489 := ReadMap(Main_m, PrtConstructFromInt(0));
    call {:si_unique_call 128} Tmp490 := PrtEquals(Tmp489, PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp490);
    goto anon9;

  anon24_Else:
    assume {:partition} !PrtFieldBool(Tmp488);
    assume {:sourceloc "", 130, 4} true;
    goto anon9;

  anon9:
    assume {:sourceloc "", 131, 4} true;
    call {:si_unique_call 129} Tmp491 := MapContainsKey(PrtConstructFromInt(1), Main_m);
    goto anon25_Then, anon25_Else;

  anon25_Then:
    assume {:partition} PrtFieldBool(Tmp491);
    assume {:sourceloc "", 131, 17} true;
    call {:si_unique_call 130} Tmp492 := ReadMap(Main_m, PrtConstructFromInt(1));
    call {:si_unique_call 131} Tmp493 := PrtEquals(Tmp492, PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp493);
    goto anon12;

  anon25_Else:
    assume {:partition} !PrtFieldBool(Tmp491);
    assume {:sourceloc "", 131, 4} true;
    goto anon12;

  anon12:
    assume {:sourceloc "", 134, 4} true;
    call {:si_unique_call 132} Tmp494 := AllocatePrtRef();
    assume PrtDynamicType(Tmp494) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp494) == 0;
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp494;
    call {:si_unique_call 133} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 135, 4} true;
    call {:si_unique_call 134} Tmp495 := AllocatePrtRef();
    assume PrtDynamicType(Tmp495) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp495) == 0;
    Main_s := Tmp495;
    assume {:sourceloc "", 136, 4} true;
    call {:si_unique_call 135} Tmp496 := AllocatePrtRef();
    assume PrtDynamicType(Tmp496) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp496) == 0;
    Main_s1 := Tmp496;
    assume {:sourceloc "", 137, 4} true;
    call {:si_unique_call 136} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(0));
    assume {:sourceloc "", 138, 4} true;
    call {:si_unique_call 137} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(1));
    assume {:sourceloc "", 139, 4} true;
    call {:si_unique_call 138} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(2));
    assume {:sourceloc "", 140, 4} true;
    call {:si_unique_call 139} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(3));
    assume {:sourceloc "", 141, 4} true;
    Tmp497 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 140} Tmp497 := InsertMap(Tmp497, PrtFieldInt(PrtConstructFromInt(0)), Main_s);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp497;
    call {:si_unique_call 141} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 145, 4} true;
    call {:si_unique_call 142} Main_i := Main_F();
    assume {:sourceloc "", 146, 4} true;
    Main_i := PrtConstructFromInt(PrtFieldInt(Main_i) + PrtFieldInt(PrtConstructFromInt(1)));
    assume {:sourceloc "", 147, 4} true;
    call {:si_unique_call 143} Tmp498 := PrtEquals(Main_i, PrtConstructFromInt(1));
    call {:si_unique_call 144} Tmp499 := PrtEquals(Main_i, PrtConstructFromInt(2));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp499) || PrtFieldBool(Tmp499)));
    assume {:sourceloc "", 148, 4} true;
    Tmp500 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 145} Tmp500 := InsertMap(Tmp500, PrtFieldInt(Main_i), Main_s1);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp500;
    call {:si_unique_call 146} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 149, 4} true;
    call {:si_unique_call 147} Tmp501 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp501);
    assume {:sourceloc "", 150, 4} true;
    call {:si_unique_call 148} Tmp502 := PrtEquals(Main_i, PrtConstructFromInt(1));
    goto anon26_Then, anon26_Else;

  anon26_Then:
    assume {:partition} PrtFieldBool(Tmp502);
    assume {:sourceloc "", 150, 17} true;
    call {:si_unique_call 149} Tmp504 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp504, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp503 := ReadSeq(Tmp504, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 150} Tmp505 := PrtEquals(Tmp503, PrtConstructFromInt(2));
    call {:si_unique_call 151} Tmp507 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp507, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp506 := ReadSeq(Tmp507, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 152} Tmp508 := PrtEquals(Tmp506, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp508) && PrtFieldBool(Tmp508)));
    goto anon15;

  anon26_Else:
    assume {:partition} !PrtFieldBool(Tmp502);
    assume {:sourceloc "", 150, 4} true;
    goto anon15;

  anon15:
    assume {:sourceloc "", 151, 4} true;
    call {:si_unique_call 153} Tmp509 := PrtEquals(Main_i, PrtConstructFromInt(2));
    goto anon27_Then, anon27_Else;

  anon27_Then:
    assume {:partition} PrtFieldBool(Tmp509);
    assume {:sourceloc "", 151, 17} true;
    call {:si_unique_call 154} Tmp511 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(2));
    assert SeqIndexInBounds(Tmp511, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp510 := ReadSeq(Tmp511, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 155} Tmp512 := PrtEquals(Tmp510, PrtConstructFromInt(2));
    call {:si_unique_call 156} Tmp514 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(2));
    assert SeqIndexInBounds(Tmp514, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp513 := ReadSeq(Tmp514, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 157} Tmp515 := PrtEquals(Tmp513, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp515) && PrtFieldBool(Tmp515)));
    goto anon18;

  anon27_Else:
    assume {:partition} !PrtFieldBool(Tmp509);
    assume {:sourceloc "", 151, 4} true;
    goto anon18;

  anon18:
    assume {:sourceloc "", 153, 4} true;
    call {:si_unique_call 158} Tmp516 := AllocatePrtRef();
    assume PrtDynamicType(Tmp516) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp516) == 0;
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp516;
    call {:si_unique_call 159} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 154, 4} true;
    Tmp517 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 160} Tmp517 := InsertMap(Tmp517, PrtFieldInt(PrtConstructFromInt(0)), Main_s);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp517;
    call {:si_unique_call 161} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 155, 4} true;
    Tmp518 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 162} Tmp518 := InsertMap(Tmp518, PrtFieldInt(PrtConstructFromInt(1)), Main_s1);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp518;
    call {:si_unique_call 163} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 156, 4} true;
    call {:si_unique_call 164} Tmp519 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp519);
    assume {:sourceloc "", 157, 4} true;
    Tmp520 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 165} Tmp520 := RemoveMap(Tmp520, PrtFieldInt(PrtConstructFromInt(0)));
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp520;
    call {:si_unique_call 166} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 158, 4} true;
    call {:si_unique_call 167} Tmp521 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(1));
    call {:si_unique_call 168} Tmp523 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp523, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp522 := ReadSeq(Tmp523, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 169} Tmp524 := PrtEquals(Tmp522, PrtConstructFromInt(2));
    call {:si_unique_call 170} Tmp526 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp526, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp525 := ReadSeq(Tmp526, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 171} Tmp527 := PrtEquals(Tmp525, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp527) && PrtFieldBool(Tmp527)));
    assume {:sourceloc "", 159, 4} true;
    Tmp528 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 172} Tmp528 := RemoveMap(Tmp528, PrtFieldInt(PrtConstructFromInt(1)));
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp528;
    call {:si_unique_call 173} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 160, 4} true;
    call {:si_unique_call 174} Tmp529 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(0));
    assert PrtFieldBool(Tmp529);
    assume {:sourceloc "", 162, 4} true;
    Tmp530 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 175} Tmp530 := InsertMap(Tmp530, PrtFieldInt(PrtConstructFromInt(0)), Main_s);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp530;
    call {:si_unique_call 176} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 163, 4} true;
    Tmp531 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 177} Tmp531 := InsertMap(Tmp531, PrtFieldInt(PrtConstructFromInt(1)), Main_s1);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp531;
    call {:si_unique_call 178} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 164, 4} true;
    call {:si_unique_call 179} Tmp532 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(2));
    call {:si_unique_call 180} Tmp533 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    call {:si_unique_call 181} Tmp534 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(Tmp533)), PrtConstructFromInt(2));
    call {:si_unique_call 182} Tmp536 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp536, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp535 := ReadSeq(Tmp536, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 183} Tmp537 := PrtEquals(Tmp535, PrtConstructFromInt(0));
    call {:si_unique_call 184} Tmp539 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp539, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp538 := ReadSeq(Tmp539, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 185} Tmp540 := PrtEquals(Tmp538, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp540) && PrtFieldBool(Tmp540)));
    assume {:sourceloc "", 165, 4} true;
    call {:si_unique_call 186} Tmp541 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    call {:si_unique_call 187} Tmp542 := PrtEquals(PrtConstructFromInt(PrtFieldSeqSize(Tmp541)), PrtConstructFromInt(2));
    call {:si_unique_call 188} Tmp544 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp544, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp543 := ReadSeq(Tmp544, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 189} Tmp545 := PrtEquals(Tmp543, PrtConstructFromInt(2));
    call {:si_unique_call 190} Tmp547 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp547, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp546 := ReadSeq(Tmp547, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 191} Tmp548 := PrtEquals(Tmp546, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp548) && PrtFieldBool(Tmp548)));
    assume {:sourceloc "", 168, 4} true;
    call {:si_unique_call 192} Main_i := Main_F();
    assume {:sourceloc "", 170, 4} true;
    Tmp549 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 193} Tmp549 := RemoveMap(Tmp549, PrtFieldInt(Main_i));
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp549;
    call {:si_unique_call 194} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 171, 4} true;
    call {:si_unique_call 195} Tmp550 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(1));
    assert PrtFieldBool(Tmp550);
    assume {:sourceloc "", 172, 4} true;
    call {:si_unique_call 196} Tmp552 := MapGetKeys(PrtFieldTuple1(Main_t));
    assume PrtDynamicType(Tmp552) == PrtTypeSeq3;
    assert SeqIndexInBounds(Tmp552, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp551 := ReadSeq(Tmp552, PrtFieldInt(PrtConstructFromInt(0)));
    Main_j := Tmp551;
    assume {:sourceloc "", 173, 7} true;
    call {:si_unique_call 197} Tmp553 := PrtEquals(Main_j, PrtConstructFromInt(0));
    call {:si_unique_call 198} Tmp554 := PrtEquals(Main_j, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp554) || PrtFieldBool(Tmp554)));
    assume {:sourceloc "", 175, 4} true;
    call {:si_unique_call 199} Tmp555 := PrtEquals(Main_j, PrtConstructFromInt(0));
    goto anon28_Then, anon28_Else;

  anon28_Then:
    assume {:partition} PrtFieldBool(Tmp555);
    assume {:sourceloc "", 175, 17} true;
    call {:si_unique_call 200} Tmp557 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp557, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp556 := ReadSeq(Tmp557, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 201} Tmp558 := PrtEquals(Tmp556, PrtConstructFromInt(0));
    call {:si_unique_call 202} Tmp560 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(0));
    assert SeqIndexInBounds(Tmp560, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp559 := ReadSeq(Tmp560, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 203} Tmp561 := PrtEquals(Tmp559, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp561) && PrtFieldBool(Tmp561)));
    goto anon21;

  anon28_Else:
    assume {:partition} !PrtFieldBool(Tmp555);
    assume {:sourceloc "", 176, 10} true;
    call {:si_unique_call 204} Tmp563 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp563, PrtFieldInt(PrtConstructFromInt(0)));
    Tmp562 := ReadSeq(Tmp563, PrtFieldInt(PrtConstructFromInt(0)));
    call {:si_unique_call 205} Tmp564 := PrtEquals(Tmp562, PrtConstructFromInt(2));
    call {:si_unique_call 206} Tmp566 := ReadMap(PrtFieldTuple1(Main_t), PrtConstructFromInt(1));
    assert SeqIndexInBounds(Tmp566, PrtFieldInt(PrtConstructFromInt(1)));
    Tmp565 := ReadSeq(Tmp566, PrtFieldInt(PrtConstructFromInt(1)));
    call {:si_unique_call 207} Tmp567 := PrtEquals(Tmp565, PrtConstructFromInt(3));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp567) && PrtFieldBool(Tmp567)));
    goto anon21;

  anon21:
    assume {:sourceloc "", 178, 4} true;
    call {:si_unique_call 208} Tmp568 := AllocatePrtRef();
    assume PrtDynamicType(Tmp568) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp568) == 0;
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp568;
    call {:si_unique_call 209} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 179, 4} true;
    call {:si_unique_call 210} Tmp569 := AllocatePrtRef();
    assume PrtDynamicType(Tmp569) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp569) == 0;
    Main_s := Tmp569;
    assume {:sourceloc "", 180, 4} true;
    call {:si_unique_call 211} Tmp570 := AllocatePrtRef();
    assume PrtDynamicType(Tmp570) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp570) == 0;
    Main_s1 := Tmp570;
    assume {:sourceloc "", 181, 4} true;
    call {:si_unique_call 212} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(0));
    assume {:sourceloc "", 182, 4} true;
    call {:si_unique_call 213} Main_s := InsertSeq(Main_s, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(1));
    assume {:sourceloc "", 183, 4} true;
    call {:si_unique_call 214} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(0)), PrtConstructFromInt(2));
    assume {:sourceloc "", 184, 4} true;
    call {:si_unique_call 215} Main_s1 := InsertSeq(Main_s1, PrtFieldInt(PrtConstructFromInt(1)), PrtConstructFromInt(3));
    assume {:sourceloc "", 185, 4} true;
    Tmp571 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 216} Tmp571 := InsertMap(Tmp571, PrtFieldInt(PrtConstructFromInt(0)), Main_s);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp571;
    call {:si_unique_call 217} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 186, 4} true;
    Tmp572 := PrtFieldTuple1(Main_t);
    call {:si_unique_call 218} Tmp572 := InsertMap(Tmp572, PrtFieldInt(PrtConstructFromInt(1)), Main_s1);
    tmpRhsValue_0 := PrtFieldTuple0(Main_t);
    tmpRhsValue_1 := Tmp572;
    call {:si_unique_call 219} Main_t := AllocatePrtRef();
    assume PrtDynamicType(Main_t) == PrtTypeTuple2;
    assume PrtFieldTuple0(Main_t) == tmpRhsValue_0;
    assume PrtFieldTuple1(Main_t) == tmpRhsValue_1;
    assume {:sourceloc "", 187, 4} true;
    call {:si_unique_call 220} Tmp573 := PrtEquals(PrtConstructFromInt(PrtFieldMapSize(PrtFieldTuple1(Main_t))), PrtConstructFromInt(2));
    assert PrtFieldBool(Tmp573);
    assume {:sourceloc "", 188, 4} true;
    call {:si_unique_call 221} Tmp575 := MapGetKeys(PrtFieldTuple1(Main_t));
    assume PrtDynamicType(Tmp575) == PrtTypeSeq3;
    assert SeqIndexInBounds(Tmp575, PrtFieldInt(Main_i));
    Tmp574 := ReadSeq(Tmp575, PrtFieldInt(Main_i));
    Main_j := Tmp574;
    assume {:sourceloc "", 189, 4} true;
    call {:si_unique_call 222} Tmp576 := PrtEquals(Main_j, PrtConstructFromInt(0));
    call {:si_unique_call 223} Tmp577 := PrtEquals(Main_j, PrtConstructFromInt(1));
    assert PrtFieldBool(PrtConstructFromBool(PrtFieldBool(Tmp577) || PrtFieldBool(Tmp577)));
    return;
}



procedure Main_S_exit36(actual_Main_S_exit36__payload_skip: PrtRef);



implementation Main_S_exit36(actual_Main_S_exit36__payload_skip: PrtRef)
{
  var Main_S_exit36__payload_skip: PrtRef;
  var event: int;
  var payload: PrtRef;

  anon0:
    Main_S_exit36__payload_skip := actual_Main_S_exit36__payload_skip;
    assume {:sourceloc "", 36, 7} true;
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
    call {:si_unique_call 224} Main_CallExitAction();
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
    call {:si_unique_call 225} Main_S_exit36(null);
    return;

  anon2_Else:
    assume {:partition} CurrState != 0;
    return;
}



procedure {:yields} MachineThread_Main(mid: int, entryArg: PrtRef);
  modifies StateStack, CurrState, eventRaised, thisMid, Tmp361, tmpRhsValue_0, Tmp360, Tmp359, Tmp358, Main_x, Main_j, Main_i, Tmp362, Main_s1, Tmp363, Main_s, Tmp366, Tmp365, Tmp368, Tmp367, tmpRhsValue_1, Tmp364, Main_t1, Tmp371, Tmp370, Tmp373, Tmp372, Tmp369, Main_t, Tmp375, Tmp376, Tmp374, Main_ts, Tmp377, Main_m, registerEvents, machineEvToQCount, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



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
    Tmp361 := PrtConstructFromInt(0);
    tmpRhsValue_0 := Tmp361;
    call {:si_unique_call 226} Tmp360 := AllocatePrtRef();
    assume PrtDynamicType(Tmp360) == PrtTypeTuple1;
    assume PrtFieldTuple0(Tmp360) == tmpRhsValue_0;
    Tmp359 := Tmp360;
    tmpRhsValue_0 := Tmp359;
    call {:si_unique_call 227} Tmp358 := AllocatePrtRef();
    assume PrtDynamicType(Tmp358) == PrtTypeTuple1;
    assume PrtFieldTuple0(Tmp358) == tmpRhsValue_0;
    Main_x := Tmp358;
    Main_j := PrtConstructFromInt(0);
    Main_i := PrtConstructFromInt(0);
    call {:si_unique_call 228} Tmp362 := AllocatePrtRef();
    assume PrtDynamicType(Tmp362) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp362) == 0;
    Main_s1 := Tmp362;
    call {:si_unique_call 229} Tmp363 := AllocatePrtRef();
    assume PrtDynamicType(Tmp363) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp363) == 0;
    Main_s := Tmp363;
    call {:si_unique_call 230} Tmp366 := AllocatePrtRef();
    assume PrtDynamicType(Tmp366) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp366) == 0;
    Tmp365 := Tmp366;
    call {:si_unique_call 231} Tmp368 := AllocatePrtRef();
    assume PrtDynamicType(Tmp368) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp368) == 0;
    Tmp367 := Tmp368;
    tmpRhsValue_0 := Tmp365;
    tmpRhsValue_1 := Tmp367;
    call {:si_unique_call 232} Tmp364 := AllocatePrtRef();
    assume PrtDynamicType(Tmp364) == PrtTypeTuple2;
    assume PrtFieldTuple0(Tmp364) == tmpRhsValue_0;
    assume PrtFieldTuple1(Tmp364) == tmpRhsValue_1;
    Main_t1 := Tmp364;
    call {:si_unique_call 233} Tmp371 := AllocatePrtRef();
    assume PrtDynamicType(Tmp371) == PrtTypeSeq3;
    assume PrtFieldSeqSize(Tmp371) == 0;
    Tmp370 := Tmp371;
    call {:si_unique_call 234} Tmp373 := AllocatePrtRef();
    assume PrtDynamicType(Tmp373) == PrtTypeMap5;
    assume PrtFieldMapSize(Tmp373) == 0;
    Tmp372 := Tmp373;
    tmpRhsValue_0 := Tmp370;
    tmpRhsValue_1 := Tmp372;
    call {:si_unique_call 235} Tmp369 := AllocatePrtRef();
    assume PrtDynamicType(Tmp369) == PrtTypeTuple2;
    assume PrtFieldTuple0(Tmp369) == tmpRhsValue_0;
    assume PrtFieldTuple1(Tmp369) == tmpRhsValue_1;
    Main_t := Tmp369;
    Tmp375 := PrtConstructFromInt(0);
    Tmp376 := PrtConstructFromInt(0);
    tmpRhsValue_0 := Tmp375;
    tmpRhsValue_1 := Tmp376;
    call {:si_unique_call 236} Tmp374 := AllocatePrtRef();
    assume PrtDynamicType(Tmp374) == PrtTypeTuple2;
    assume PrtFieldTuple0(Tmp374) == tmpRhsValue_0;
    assume PrtFieldTuple1(Tmp374) == tmpRhsValue_1;
    Main_ts := Tmp374;
    call {:si_unique_call 237} Tmp377 := AllocatePrtRef();
    assume PrtDynamicType(Tmp377) == PrtTypeMap4;
    assume PrtFieldMapSize(Tmp377) == 0;
    Main_m := Tmp377;
    registerEvents[0][0] := false;
    registerEvents[0][1] := false;
    call {:si_unique_call 238} Main_S_entry36(entryArg);
    goto anon5_LoopHead;

  anon5_LoopHead:
    goto anon5_LoopDone, anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} true;
    yield;
    call {:si_unique_call 239} event, payload := Dequeue();
    call {:si_unique_call 240} Main_ProbeStateStack(event);
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} CurrState == 0;
    goto Main_S;

  Main_S:
    goto anon7_Then, anon7_Else;

  anon7_Then:
    assume {:partition} event == 0;
    return;

  anon7_Else:
    assume {:partition} event != 0;
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



procedure {:yields} {:entrypoint} main();
  modifies machineCounter, machineToQCAssert, machineToQCAssume, machineEvToQCount, StateStack, CurrState, eventRaised, thisMid, Tmp361, tmpRhsValue_0, Tmp360, Tmp359, Tmp358, Main_x, Main_j, Main_i, Tmp362, Main_s1, Tmp363, Main_s, Tmp366, Tmp365, Tmp368, Tmp367, tmpRhsValue_1, Tmp364, Main_t1, Tmp371, Tmp370, Tmp373, Tmp372, Tmp369, Main_t, Tmp375, Tmp376, Tmp374, Main_ts, Tmp377, Main_m, registerEvents, MachineInboxHead, MachineInboxTail, MachineInboxStoreEvent;



implementation {:entrypoint} main()
{
  var tmpRhsValue: PrtRef;

  anon0:
    machineCounter := 0;
    yield;
    call {:si_unique_call 241} tmpRhsValue := newMachine_Main(null);
    return;
}






