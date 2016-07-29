// Common code for P semantics

// Sequences
procedure {:inline} WriteSeq(seq: PrtRef, index: int, value: PrtRef)  returns (nseq: PrtRef);
procedure {:inline} InsertSeq(seq: PrtRef, index: int, value: PrtRef)  returns (nseq: PrtRef);
procedure {:inline} RemoveSeq(seq: PrtRef, index: int)  returns (nseq: PrtRef);


// Maps
procedure {:inline} MapContainsKey(map: PrtRef, key: PrtRef) returns (v: bool);
procedure {:inline} ReadMap(map: PrtRef, key: PrtRef) returns (value: PrtRef);
procedure {:inline} MapGetKeys(map: PrtRef) returns (seq: PrtRef);
procedure {:inline} MapGetValues(map: PrtRef) returns (seq: PrtRef);

procedure {:inline} WriteMap(map: PrtRef, key: PrtRef, value: PrtRef)  returns (nmap: PrtRef);
procedure {:inline} InsertMap(map: PrtRef, key: PrtRef, value: PrtRef)  returns (nmap: PrtRef);
procedure {:inline} RemoveMap(map: PrtRef, key: PrtRef)  returns (nmap: PrtRef);


//The global counter for machines.
var machineCounter : int;

// The Queues

// MachineId -> index -> EventId
var MachineInboxStoreEvent: [int][int]int;

// MachineId -> index -> Payload
var MachineInboxStorePayload: [int][int]PrtRef;

// MachineId -> head index
var MachineInboxHead: [int]int;

// MachineId -> tail index
var MachineInboxTail: [int]int;

//Queue Constraints
var machineToQCAssert: [int] int;
var machineToQCAssume: [int] int;
var machineEvToQCount: [int][int]int;


//mid
var {:thread_local} thisMid : int;

//For raised events.
var {:thread_local} eventRaised: bool;
var {:thread_local} raisedEvent: int;
var {:thread_local} raisedEventPl: PrtRef;


procedure {:inline} InitializeInbox(mid: int)
{
   assume MachineInboxHead[mid] == 1;
   assume MachineInboxTail[mid] == 0;
}

// State stack
type {:datatype} StateStackType;
function {:constructor} Nil(): StateStackType;
function {:constructor} Cons(state: int, stack: StateStackType): StateStackType;

var {:thread_local} StateStack: StateStackType;
var {:thread_local} CurrState: int;


procedure StateStackPush(state: int) 
{
   StateStack := Cons(state, StateStack);
}

procedure StateStackPop()
{
   assert StateStack != Nil();
   StateStack := stack#Cons(StateStack);
   return;
}

procedure Probe(event: int) (returns handlerState: int)
{
   handlerState := CurrState;
   if(registerEvents[handlerState][event])
   {
      return;
   }

   var s: StateStackType;
   s := StateStack;
   while(s != Nil()) 
   {
      handlerState := state#Cons(StateStack);
      s := stack#Cons(StateStack);
	  if(registerEvents[handlerState][event])
	  {
         return;
      }
   }
   assert false; //No handler
   return;
}


procedure AssertEventCard(mid: int, event: int)
{
   var head: int;
   var tail: int;
   var count: int;
   
   head := MachineInboxHead[mid];
   tail := MachineInboxTail[mid];
   count := machineEvToQCount[mid][event];

   //Queue constraints for specific events.
}

procedure AssertMachineQueueSize(mid: int)
{
	var head: int;
	var tail: int;
    var size: int;
    var qc: int;

    head := MachineInboxHead[mid];
    tail := MachineInboxTail[mid];
    size := (tail - head) + 1;

	qc := machineToQCAssert[mid];
	if(qc > 0)
	{
       assert (size <= qc);
	}

    qc := machineToQCAssume[mid];
	if(qc > 0)
	{
       assume (size <= qc);
	}
}

procedure Enqueue(mid:int, event: int, payload: PrtRef) 
{
   var q: int;
   var tail: int;

   tail := MachineInboxTail[mid] + 1;
   MachineInboxTail[mid] := tail;
   
   q := machineEvToQCount[mid][event] + 1;
   machineEvToQCount[mid][event] := q;
   MachineInboxStoreEvent[mid][tail] := event;
   MachineInboxStorePayload[mid][tail] := payload;

   call AssertEventCard(mid, event);
   call AssertMachineQueueSize(mid);
}

procedure send(mid: int, event: int, payload: PrtRef)
{
	call monitor(event, payload);
	call Enqueue(mid, event, payload);
}
