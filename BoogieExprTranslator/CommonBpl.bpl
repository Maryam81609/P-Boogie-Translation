// Common code for P semantics
//Deep copy is guarenteed because, every time we mutate a value, we create a new PrtRef for it.

// Sequences
procedure {:inline} WriteSeq(seq: PrtRef, index: int, value: PrtRef)  returns (nseq: PrtRef)
{
	var store: [int]PrtRef;
	var size: int;

	assert SeqIndexInBounds(seq, index);
		
	size := PrtFieldSeqSize(seq);
	store := PrtFieldSeqStore(seq);
	store[index] := value;

	call nseq := AllocatePrtRef();
	assume PrtDynamicType(nseq) == PrtDynamicType(seq);
	assume PrtFieldSeqSize(nseq) == size;
	assume PrtFieldSeqStore(nseq) == store;
	return;
}

procedure {:inline} RemoveSeq(seq: PrtRef, index: int)  returns (nseq: PrtRef)
{
	var oldStore: [int]PrtRef;
	var newStore: [int]PrtRef;
	var size: int;
	var i: int;
	
	size := PrtFieldSeqSize(seq);
	i := 0;
	oldStore := PrtFieldSeqStore(seq);

	assert SeqIndexInBounds(seq, index);

	while(i < index)
	{
		newStore[i] := oldStore[i];
		i := i + 1;
	}
	while(i < (size - 1))
	{
		newStore[i] := oldStore[i + 1];
		i := i + 1;
	}

	call nseq := AllocatePrtRef();
	assume PrtDynamicType(nseq) == PrtDynamicType(seq);
	assume PrtFieldSeqSize(nseq) == size - 1;
	assume PrtFieldSeqStore(nseq) == newStore;
	return;
}

procedure {:inline} InsertSeq(seq: PrtRef, index: int, value: PrtRef)  returns (nseq: PrtRef)
{
	var oldStore: [int]PrtRef;
	var newStore: [int]PrtRef;
	var size: int;
	var i: int;

	size := PrtFieldSeqSize(seq);
	i := 0;    
	assert (0 <= index && index <= size);
	
	oldStore := PrtFieldSeqStore(seq);
	while(i < index)
	{
		newStore[i] := oldStore [i];
		i := i + 1;
	}
	
	newStore[index] := value;
	i := i + 1;

	while(i < size)
	{
		newStore[i + 1] := oldStore[i];
		i := i + 1;
	}

	call nseq := AllocatePrtRef();
	assume PrtFieldSeqSize(nseq) == size + 1;
	assume PrtFieldSeqStore(nseq) == newStore;
	assume PrtDynamicType(nseq) == PrtDynamicType(seq);
}



// Maps
procedure {:inline} MapContainsKey(map: PrtRef, key: PrtRef) returns (v: PrtRef)
{
	var size: int;
	var i: int;
	var keys: [int]PrtRef;

	v := PrtFalse;
	size := PrtFieldMapSize(map);
	i := 0;
	keys := PrtFieldMapKeys(map);

	while(i < size)
	{
		if(keys[i] == key)
		{
			v := PrtTrue;
			return;
		}
		i := i + 1;
	}
	return;
}

procedure {:inline} ReadMap(map: PrtRef, key: PrtRef) returns (value: PrtRef)
{
	var size: int;
	var i: int;
	var keys: [int]PrtRef;
	var values: [int]PrtRef;

	size := PrtFieldMapSize(map);
	i := 0;
	keys := PrtFieldMapKeys(map);
	values := PrtFieldMapValues(map);

	while(i < size)
	{
		if(keys[i] == key)
		{
			value := values[i];
			return;
		}
		i := i + 1;
	}

	assert false;
	return;
}

procedure {:inline} MapGetKeys(map: PrtRef) returns (seq: PrtRef)
{
	var size: int;
	var store: [int]PrtRef;

	store := PrtFieldMapKeys(map);
	size := PrtFieldMapSize(map);

	call seq := AllocatePrtRef();
	assume PrtFieldSeqStore(seq) == store; 
	assume PrtFieldSeqSize(seq) == size;

	return;
}
procedure {:inline} MapGetValues(map: PrtRef) returns (seq: PrtRef)
{
	var size: int;
	var store: [int]PrtRef;

	store := PrtFieldMapValues(map);
	size := PrtFieldMapSize(map);

	call seq := AllocatePrtRef();
	assume PrtFieldSeqStore(seq) == store; 
	assume PrtFieldSeqSize(seq) == size;

	return;
}

procedure {:inline} WriteMap(map: PrtRef, key: PrtRef, value: PrtRef)  returns (nmap: PrtRef)
{
	var size: int;
	var i: int;
	var flag: bool;
	var keys: [int]PrtRef;
	var values: [int]PrtRef;

	size := PrtFieldMapSize(map);
	i := 0;
	keys := PrtFieldMapKeys(map);
	values := PrtFieldMapValues(map);
	flag := false;

	while(i < size)
	{
		if(keys[i] == key)
		{
			values[i] := value;
			flag := true;
		}
		i := i + 1;
	}

	if(!flag)
	{
	    call {:cexpr "key_not_found"} boogie_si_record_bool(true);
		keys[i] := key;
		values[i] := value;
		size := size + 1;
	}

	call nmap := AllocatePrtRef();
	assume PrtDynamicType(nmap) == PrtDynamicType(map);
	assume PrtFieldMapSize(nmap) == size;
	assume PrtFieldMapKeys(nmap) == keys;
	assume PrtFieldMapValues(nmap) == values;

	return;
}

procedure {:inline} InsertMap(map: PrtRef, key: PrtRef, value: PrtRef)  returns (nmap: PrtRef)
{
	var size: int;
	var i: int;
	var keys: [int]PrtRef;
	var values: [int]PrtRef;

	size := PrtFieldMapSize(map);
	i := 0;
	keys := PrtFieldMapKeys(map);
	values := PrtFieldMapValues(map);
	
	while(i < size)
	{
		if(keys[i] == key)
		{
			assert false;
		}
		i := i + 1;
	}
	
	keys[size] := key;
	values[size] := value;

	call nmap := AllocatePrtRef();
	assume PrtDynamicType(nmap) == PrtDynamicType(map);
	assume PrtFieldMapSize(nmap) == size + 1;
	assume PrtFieldMapKeys(nmap) == keys;
	assume PrtFieldMapValues(nmap) == values;

	return;
}

procedure {:inline} RemoveMap(map: PrtRef, key: PrtRef)  returns (nmap: PrtRef)
{
	var size: int;
	var i: int;
	var flag: bool;
	var oldKeys: [int]PrtRef;
	var oldValues: [int]PrtRef;
	var newKeys: [int]PrtRef;
	var newValues: [int]PrtRef;

	size := PrtFieldMapSize(map);
	assert (size > 0);
	i := 0;
	oldKeys := PrtFieldMapKeys(map);
	oldValues := PrtFieldMapValues(map);
	flag := false;

	while(i < size && oldKeys[i] != key)
	{
		newKeys[i] := oldKeys[i];
		newValues[i] := oldValues[i];
		if(oldKeys[i] == key)
		{
			flag := true;
			newKeys[i] := oldKeys[size - 1];
			newValues[i] := oldValues[size - 1];
		}
		i := i + 1;
	}
	assert flag;

	while(i < (size - 1))
	{
		newKeys[i] := oldKeys[i + 1];
		newValues[i] := oldValues[i + 1];
		i := i + 1;
	}

	call nmap := AllocatePrtRef();
	assume PrtDynamicType(nmap) == PrtDynamicType(map);
	assume PrtFieldMapSize(nmap) == size - 1;
	assume PrtFieldMapKeys(nmap) == newKeys;
	assume PrtFieldMapValues(nmap) == newValues;

	return;
}


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

//For event variables
var {:thread_local} tmpEventID: int;

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
	yield;
	call Enqueue(mid, event, payload);
}
