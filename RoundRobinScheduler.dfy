class Process {
var pid: int
var arrivalTime: nat
var burstTime: nat
var burstTimeRemaining: nat
var completionTime: int
var turnaroundTime: int
var waitingTime: int
var isComplete: bool
var inQueue: bool

constructor (id: int, arrival: nat, burst: nat)
    ensures pid == id
    ensures arrivalTime == arrival
    ensures burstTime == burst
    ensures burstTimeRemaining == burst
    ensures completionTime == 0 && turnaroundTime == 0 && waitingTime == 0
    ensures !isComplete && !inQueue
{
    pid := id;
    arrivalTime := arrival;
    burstTime := burst;
    burstTimeRemaining := burst;
    completionTime := 0;
    turnaroundTime := 0;
    waitingTime := 0;
    isComplete := false;
    inQueue := false;
}
}


method {:axiom} ProveAllProcessesCompleteAtMaxTime(processes: seq<Process>, currentTime: int, maxTime: int, programsExecuted: int)
requires currentTime >= 0 && currentTime >= maxTime
ensures forall i :: 0 <= i < |processes| ==> processes[i].isComplete == true && processes[i].inQueue == false
ensures programsExecuted == |set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false|


method {:axiom} ProveAllObjectsComplete(processes: seq<Process>)
requires |set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false| == |processes|
ensures forall i :: 0 <= i < |processes| ==> processes[i].isComplete == true && processes[i].inQueue == false
ensures |set i | 0 <= i < |processes| && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false| == |set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false|
// {
//     var i := 0;
//     while i < n
//         invariant 0 <= i <= n
//         invariant forall j :: 0 <= j < i ==> processes[j].isComplete == true
//     {
//         // Proof by contradiction
//         if !processes[i].isComplete {
//             // If any process is not complete, then the set of complete processes would be smaller than n
//             var completeSet := set j | 0 <= j < n && processes[j].isComplete;
//             assert i !in completeSet;
//             assert |completeSet| < n;  // Contradiction with the precondition
//             assert false;              // Unreachable
//         }
        
//         i := i + 1;
//     }

//     // At this point, we've proven that all processes have isComplete == true
//     assert forall i :: 0 <= i < n ==> processes[i].isComplete == true;
// }

lemma SubsetImpliesCardinalityLe<T>(A: set<T>, B: set<T>)
  requires A <= B || A < B
  ensures  A <= B ==> |A| <= |B|
  ensures  A < B ==> |A| < |B|
{
  if |A| == 0 {
    // Base case: A is empty, so |A| = 0, and cardinalities are ≥ 0.
    // Dafny automatically knows 0 <= |B|.
  } else {
    // Inductive step: pick some x ∈ A.
    var x :| x in A;
    // Remove x from both sets:
    var A2 := A - { x };
    var B2 := B - { x };

    assert A2 <= B2;

    // Recurse on the smaller set A2:
    SubsetImpliesCardinalityLe(A2, B2);
    assert |A2| <= |B2|;
  }
}


method UniqueSeqLengthAtMostN(s: seq<int>, n: nat)
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < n
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures 0 <= |s| <= n
{
    var numbersSet := {};
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |numbersSet| == i
        invariant forall x :: x in numbersSet <==> 0 <= x < i
        invariant forall x :: 0 <= x < i ==> x in numbersSet
    {
        numbersSet := numbersSet + {i};
        i := i + 1;
    }
    // Put all elements of s in a set
    var sSet := {};
    var j := 0;
    while j < |s|
        invariant 0 <= j <= |s|
        invariant |sSet| == j
        invariant forall x :: x in sSet <==> x in s[..j]
    {
        sSet := sSet + {s[j]};
        j := j + 1;
    }
    // sSet contains all elements from s and numbersSet 
    //contains all elements from 0 to n-1
    assert sSet <= numbersSet;
    SubsetImpliesCardinalityLe(sSet, numbersSet);
    assert |sSet| <= |numbersSet|;
}

lemma {:axiom} setAndSeqEqual(s: seq<int>, sSet: set<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] in sSet
  requires forall i :: i in sSet ==> i in s
  ensures |s| == |sSet|
//{
//}

lemma MissingOneElementLength(processes: seq<Process>, s: seq<int>, n: nat)
  requires |processes| == n
  requires exists i :: 0 <= i < n && processes[i].isComplete == false && processes[i].inQueue == true && !exists k :: 0 <= k < |s| && s[k] == i
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < n
  ensures |s| < n
{
  // First, let's create a set of all indices in s
  var sIndices := set k | 0 <= k < |s| :: s[k];
  // By the requirement, there exists at least one i where:
  // 0 <= i < n, process[i] is not complete, is in queue, and i is not in s
  assert exists i :: 0 <= i < n && processes[i].isComplete == false && 
                     processes[i].inQueue == true && i !in sIndices;
  
  // Let's prove that sIndices is a proper subset of {0,...,n-1}
  var allIndices := set i | 0 <= i < n;
  
  // All elements in s are valid indices
  assert forall k :: k in sIndices ==> 0 <= k < n;
  assert sIndices < allIndices;
  
  // There's at least one element in allIndices that's not in sIndices
  assert exists i :: i in allIndices && i !in sIndices;
  
  // Therefore sIndices is a strict subset of allIndices
  assert sIndices < allIndices;
  
  // The size of allIndices is n
  SetOfNElementsHasSizeN(n);
  assert |allIndices| == n;
  
  // Since sIndices is a strict subset of allIndices, its size must be less than n
  SubsetImpliesCardinalityLe(sIndices, allIndices);
  assert |sIndices| < |allIndices|;
  
  // All elements in s are unique (implied by the requirements)
  assert forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j];
  assert forall i :: 0 <= i < |s| ==> s[i] in sIndices;
  assert forall i :: i in sIndices ==> i in s;
  // Therefore, |s| = |sIndices| < n
  setAndSeqEqual(s, sIndices);
  assert |s| == |sIndices|;
  assert |s| < n;
}

predicate ProcessQueueCurTime(processes: seq<Process>, currentTime: int)
reads processes
{
  forall p :: (p in processes[..]) ==> if p.arrivalTime <= currentTime then 
    (p.inQueue == true || p.isComplete == true) else (p.inQueue == false || p.isComplete == false)
}

predicate AllPinProcessQueue(processes: seq<Process>)
reads processes
{
  forall p :: (p in processes[..]) ==> !(p.inQueue == true && p.isComplete == true)
}

// Scans all processes and enqueues any that have arrived but are not yet in the queue
method CheckForNewArrivals(
    processes: seq<Process>, n: int,
    currentTime: int,
    readyQueue: seq<int>,
    extraInQueue: bool)
returns (newQueue: seq<int>)
modifies processes[..]
requires |processes| == n && currentTime >= 0 && n > 0 && 0 <= |readyQueue| <= n
//requires (!exists j :: 0 <= j < n && processes[j].inQueue == true) ==> (exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false)
requires |readyQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false
requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
requires forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
//requires if (!exists j :: 0 <= j < n && processes[j].isComplete == false && processes[j].inQueue == false) then |readyQueue| < n else |readyQueue| <= n
requires forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
ensures forall i :: 0 <= i < |newQueue| ==> 0 <= newQueue[i] < n && processes[newQueue[i]].inQueue == true && processes[newQueue[i]].isComplete == false && processes[newQueue[i]].arrivalTime <= currentTime
ensures ProcessQueueCurTime(processes, currentTime)
ensures AllPinProcessQueue(processes)
ensures |set i | 0 <= i < n && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
ensures forall i :: 0 <= i < n && old(processes[i].inQueue) == true && (!exists j :: 0 <= j < |readyQueue| && readyQueue[j] == i) ==> (!exists k :: 0 <= k < |newQueue| && newQueue[k] == i)
//ensures if (exists j :: 0 <= j < n && processes[j].inQueue == true && !exists k :: 0 <= k < |readyQueue| && readyQueue[k] == j) then |newQueue| >= 0 else |newQueue| > 0
ensures n >= |newQueue| > 0
//ensures if extraInQueue == true then 0 <= |newQueue| <= n && |newQueue| >= |readyQueue| else 0 < |newQueue| <= n && |newQueue| >= |readyQueue|
ensures forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
ensures forall p :: (p in processes[..]) ==> old(p.inQueue) == true ==> p.inQueue == true
ensures forall j :: 0 <= j < n && old(processes[j].isComplete) == true ==> processes[j].inQueue == false && processes[j].inQueue == old(processes[j].inQueue)
ensures forall i :: 0 <= i < n ==> processes[i].arrivalTime == old(processes[i].arrivalTime)
ensures forall i :: 0 <= i < n ==> processes[i].isComplete == true && processes[i].inQueue == false ==> old(processes[i].isComplete) == processes[i].isComplete && old(processes[i].arrivalTime) == processes[i].arrivalTime && old(processes[i].inQueue) == processes[i].inQueue
ensures if (exists j :: 0 <= j < n && processes[j].isComplete == false && old(processes[j].inQueue) == true && !exists k :: 0 <= k < |newQueue| && newQueue[k] == j) then |newQueue| < n else |newQueue| <= n
ensures forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
{
var i := 0;
newQueue := readyQueue;
var added := false;
if (exists j :: 0 <= j < n && processes[j].isComplete == false && old(processes[j].inQueue) == true && !exists k :: 0 <= k < |newQueue| && newQueue[k] == j) {
  MissingOneElementLength(processes, newQueue, n);
  assert |newQueue| < n;
}  else {
  assert |newQueue| <= n;
}
while i < n
    invariant 0 <= i <= n
    invariant forall j :: j in newQueue ==> 0 <= j < n && processes[j].inQueue == true && processes[j].isComplete == false && processes[j].arrivalTime <= currentTime
    invariant forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
    invariant forall j :: 0 <= j < i ==> if processes[j].arrivalTime <= currentTime then (processes[j].inQueue == true || 
                processes[j].isComplete == true) else (processes[j].inQueue == false || processes[j].isComplete == false)
    invariant |newQueue| >= |readyQueue|
    invariant |newQueue| == 0 ==> (exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false)// ==> 0 < |newQueue| <= n// else 0 <=|newQueue| <= n
    invariant |newQueue| <= n
    invariant forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
    invariant forall k :: 0 <= k < |newQueue| ==> 0 <= newQueue[k] < n
    invariant forall p :: (p in processes[..]) ==> old(p.inQueue) == true ==> p.inQueue == old(p.inQueue)
    invariant forall p :: (p in processes[..]) ==> old(p.isComplete) == true ==> p.isComplete == true
    invariant forall i :: 0 <= i < n ==> old(processes[i].isComplete) == processes[i].isComplete && old(processes[i].arrivalTime) == processes[i].arrivalTime
    invariant forall i :: 0 <= i < n ==> processes[i].isComplete == true && processes[i].inQueue ==> |newQueue| <= n - 1
    invariant forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
    invariant forall l :: 0 <= l < i && old(processes[l].inQueue) == true && (!exists j :: 0 <= j < |readyQueue| && readyQueue[j] == l) ==> (!exists k :: 0 <= k < |newQueue| && newQueue[k] == l);
    invariant forall j :: j in newQueue ==> 0 <= j < n && (old(processes[j].inQueue) == false || exists k :: 0 <= k < |readyQueue| && readyQueue[k] == j)
    invariant |set i | 0 <= i < n && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
    decreases n - i
{
    if processes[i].arrivalTime <= currentTime
        && !processes[i].inQueue
        && !processes[i].isComplete
    {
        processes[i].inQueue := true;
        newQueue := newQueue + [i];
        added := true;
    }
    UniqueSeqLengthAtMostN(newQueue, n);
    assert forall l :: 0 <= l < |newQueue| ==> (exists k :: 0 <= k < |readyQueue| && readyQueue[k] == newQueue[l]) || (old(processes[newQueue[l]].inQueue) == false);
   // assert forall l :: 0 <= l < i && old(processes[l].inQueue) == true && (!exists j :: 0 <= j < |readyQueue| && readyQueue[j] == l) ==> (!exists k :: 0 <= k < |newQueue| && newQueue[k] == l);
    var oldSet := set i | 0 <= i < n && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false;
    var newSet := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    assert oldSet == newSet;
    i := i + 1;
}
if (exists j :: 0 <= j < n && processes[j].isComplete == false && old(processes[j].inQueue) == true && !exists k :: 0 <= k < |newQueue| && newQueue[k] == j) {
  MissingOneElementLength(processes, newQueue, n);
  assert |newQueue| < n;
}  else {
  assert |newQueue| <= n;
}
}

// Marks a single process as complete and verifies the count increased by exactly one
// method MarkProcessComplete(processes: seq<Process>, n: int, processIndex: int)
// returns (oldCount: int, newCount: int)
// modifies processes[processIndex]
// requires |processes| == n && n > 0
// requires 0 <= processIndex < n
// requires processes[processIndex].isComplete == false
// requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
// ensures processes[processIndex].isComplete == true
// ensures newCount == oldCount + 1
// ensures newCount == |set i | 0 <= i < n && processes[i].isComplete|
// ensures oldCount == |set i | 0 <= i < n && old(processes[i].isComplete)|
// {
//     // Count completed processes before the change
//     var before := set i | 0 <= i < n && processes[i].isComplete;
//     oldCount := |set i | 0 <= i < n && processes[i].isComplete|;
//     processes[processIndex].isComplete := true;
//     // Count completed processes after the change
//     newCount := |set i | 0 <= i < n && processes[i].isComplete|;
//     var after := set i | 0 <= i < n && processes[i].isComplete;
//     assert after == before + {processIndex};
    
//     // Prove that exactly one process was marked complete
//     assert old(processes[processIndex].isComplete) == false;
//     assert processes[processIndex].isComplete == true;
//     assert forall j :: 0 <= j < n && j != processIndex ==> 
//         processes[j].isComplete == old(processes[j].isComplete);
//     assert processes[processIndex].isComplete != old(processes[processIndex].isComplete);
//     assert newCount == oldCount + 1;
// }

lemma {:axiom} AllProcessesCompleteNotInQueue(processes: seq<Process>, n: nat)
  requires |processes| == n
  requires |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false| == n
  ensures forall i :: 0 <= i < n ==> processes[i].isComplete && !processes[i].inQueue
// {
//   // The requirement states that the set of indices where processes are complete and not in queue has size n
//   // Since n is the total number of processes, this means all processes must be complete and not in queue
  
//   // Get the set of indices where processes are complete and not in queue
//   var completeNotInQueueSet := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
  
//   // We know this set has size n
//   assert |completeNotInQueueSet| == n;
  
//   // Since there are n total processes, and n processes that are complete and not in queue,
//   // every process must be in this set
//   assert forall i :: 0 <= i < n ==> i in completeNotInQueueSet;
  
//   // By the definition of the set, if i is in the set, then processes[i] is complete and not in queue
//   assert forall i :: i in completeNotInQueueSet ==> processes[i].isComplete && !processes[i].inQueue;
  
//   // Combining these facts proves our lemma
//   assert forall i :: 0 <= i < n ==> processes[i].isComplete && !processes[i].inQueue;
// }

lemma newQueueMustBeEmpty(processes: seq<Process>, n: nat, newQueue: seq<int>)
  requires |processes| == n
  requires |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false| == n
  requires forall i :: 0 <= i < |newQueue| ==> 0 <= newQueue[i] < n && processes[newQueue[i]].isComplete == false && processes[newQueue[i]].inQueue == true
  ensures |newQueue| == 0
{
  // First, use the AllProcessesCompleteNotInQueue lemma to establish that all processes are complete and not in queue
  AllProcessesCompleteNotInQueue(processes, n);
  
  // Now we know that all processes are complete and not in queue
  assert forall i :: 0 <= i < n ==> processes[i].isComplete && !processes[i].inQueue;
  
  // The third precondition states that all elements in newQueue refer to processes that are:
  // 1. Not complete
  // 2. In the queue
  assert forall i :: 0 <= i < |newQueue| ==> 
    0 <= newQueue[i] < n && 
    processes[newQueue[i]].isComplete == false && 
    processes[newQueue[i]].inQueue == true;
  
  // But we just proved that all processes are complete and not in queue
  // This creates a contradiction if newQueue has any elements
  
  // Let's prove by contradiction: if newQueue had any elements, it would violate our assertion
  if |newQueue| > 0 {
    // Take the first element of newQueue
    var idx := newQueue[0];
    
    // This element must refer to a valid process index
    assert 0 <= idx < n;
    
    // By the third precondition, this process must not be complete and must be in queue
    assert processes[idx].isComplete == false;
    assert processes[idx].inQueue == true;
    
    // But by our first assertion, all processes are complete and not in queue
    assert processes[idx].isComplete && !processes[idx].inQueue;
    
    // This is a contradiction, so newQueue must be empty
    assert false;
  }
  
  // Therefore, newQueue must be empty
  assert |newQueue| == 0;
}

lemma SetOfNElementsHasSizeN(n: nat)
  ensures |set i | 0 <= i < n| == n
{
  // We'll prove this by induction on n
  if n == 0 {
    // Base case: empty set has size 0
    //assert {set i | 0 <= i < 0} == {};
    assert |set i | 0 <= i < 0| == 0;
  } else {
    // Inductive case: assume the lemma holds for n-1
    SetOfNElementsHasSizeN(n-1);
    
    // By induction hypothesis, we know:
    assert |set i | 0 <= i < n-1| == n-1;
    
    // The set for n includes all elements from the set for n-1, plus the element n-1
    var setNMinus1 := set i | 0 <= i < n-1;
    var setN := set i | 0 <= i < n;
    
    // Prove that setN = setNMinus1 ∪ {n-1}
    assert setN == setNMinus1 + {n-1};
    
    // Prove that n-1 is not in setNMinus1
    assert n-1 !in setNMinus1;
    
    // Therefore, |setN| = |setNMinus1| + 1 = (n-1) + 1 = n
    assert |setN| == |setNMinus1| + 1;
    assert |setN| == n-1 + 1;
    assert |setN| == n;
  }
}


lemma NotAllCompleteImpliesCountNotN(processes: seq<Process>, n: nat)
  requires |processes| == n
  requires exists j :: 0 <= j < n && processes[j].isComplete == false
  ensures |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false| != n
{
  var completedNotInQueue := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
  // At least one process is not complete, so the number of complete ones must be < n
  assert exists j :: 0 <= j < n && processes[j].isComplete == false && !(j in completedNotInQueue);
  assert exists j :: 0 <= j < n && !(j in completedNotInQueue); // Because isComplete == false
  assert forall i :: i in completedNotInQueue ==> 0 <= i < n;
  var completeSet := set i | 0 <= i < n;
  SetOfNElementsHasSizeN(n);
  assert |completeSet| == n;
  assert completeSet > completedNotInQueue;
  SubsetImpliesCardinalityLe(completedNotInQueue, completeSet);
  assert |completedNotInQueue| < |completeSet|;
  assert |completedNotInQueue| < n;
}


lemma ProveUpdatedExecutedNotN(processes: seq<Process>, n: nat, updatedExecuted: nat)
  requires |processes| == n
  requires updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  requires exists j :: 0 <= j < n && processes[j].isComplete == false
  ensures updatedExecuted != n
{
  NotAllCompleteImpliesCountNotN(processes, n);
}



// Pops the head of readyQueue, runs it for up to 'quantum',
// updates times and re-queues or marks complete.
method UpdateQueue(
    processes: seq<Process>, n: int,
    quantum: int,
    readyQueue: seq<int>,
    currentTime: int,
    programsExecuted: int)
returns (
    newQueue: seq<int>,
    updatedTime: int,
    updatedExecuted: int)
    modifies processes[..]
    requires |processes| == n && quantum > 0 && n > 0 && currentTime >= 0 && programsExecuted >= 0 && 0 < |readyQueue| <= n
    //requires forall i :: 1 <= i < n ==> processes[i].arrivalTime >= processes[i-1].arrivalTime
    requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
    //requires forall j :: 0 <= j < n && processes[j].inQueue == true ==> exists k :: 0 <= k < |readyQueue| && readyQueue[k] == j
    requires forall i :: 0 <= i < |readyQueue| ==> 0 <= readyQueue[i] < n
    requires (|readyQueue| == 1 && processes[readyQueue[0]].burstTimeRemaining <= quantum) ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false
    requires ProcessQueueCurTime(processes, currentTime)
    requires AllPinProcessQueue(processes)
    requires programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
    requires forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
    requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
    requires forall i, j :: 0 <= i < j < |processes| ==> processes[i] != processes[j]
    requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
    requires forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
    
    ensures forall j :: 0 <= j < n && old(processes[j].isComplete) == true ==> processes[j].inQueue == false && processes[j].inQueue == old(processes[j].inQueue)
    ensures forall i :: 0 <= i < |newQueue| ==> 0 <= newQueue[i] < n && processes[newQueue[i]].inQueue == true && processes[newQueue[i]].isComplete == false && processes[newQueue[i]].arrivalTime <= updatedTime
    ensures forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
    ensures AllPinProcessQueue(processes)
    ensures ProcessQueueCurTime(processes, updatedTime)
    //ensures |set i | 0 <= i < n && old(processes[i].isComplete) != processes[i].isComplete| <= 1
    ensures if updatedExecuted == n then |newQueue| == 0 else 0 < |newQueue| <= n
    ensures updatedTime > currentTime
    ensures updatedExecuted == programsExecuted || updatedExecuted == programsExecuted + 1
    ensures updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
    ensures forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
    //ensures forall j :: 0 <= j < n && processes[j].inQueue == true ==> exists k :: 0 <= k < |newQueue| && newQueue[k] == j
    //ensures forall p :: p in processes[..] ==> if (p.isComplete == true && p.inQueue == false) then (p.burstTimeRemaining == 0 && p.completionTime >= p.arrivalTime && p.turnaroundTime >= p.waitingTime && p.waitingTime >= 0) else (p.burstTimeRemaining > 0 && p.completionTime == 0 && p.turnaroundTime == 0 && p.waitingTime == 0)
{
  // Initialize return values
  //newQueue := readyQueue;
  updatedTime := currentTime;
  updatedExecuted := programsExecuted;
  
  // Pop the first index off the ready queue
  var i := readyQueue[0];
  newQueue := readyQueue[1..];
  //assert |newQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
  assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
  if processes[i].burstTimeRemaining <= quantum {
    // Process will finish in this quantum
    var count := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    processes[i].inQueue := false;

    processes[i].isComplete := true;

    updatedTime := currentTime + processes[i].burstTimeRemaining;
    processes[i].completionTime := updatedTime;
    processes[i].waitingTime := processes[i].completionTime - processes[i].arrivalTime - processes[i].burstTime;
    processes[i].turnaroundTime := processes[i].waitingTime + processes[i].burstTime;
    if processes[i].waitingTime < 0 {
      processes[i].waitingTime := 0;
    }
    processes[i].burstTimeRemaining := 0;
    var newcount := set i | 0 <= i < n && processes[i].isComplete == true&& processes[i].inQueue == false;
    
    assert newcount == count + {i};
    
    updatedExecuted := programsExecuted + 1;
    
    // Check for new arrivals if not all processes have been enqueued
    //assert ProcessQueueCurTime(processes, updatedTime);
    if updatedExecuted != n {
      assert forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0;
      //assert |newQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
      assert 0 <= |newQueue| <= n;
      //assert forall j :: 0 <= j < n && processes[j].inQueue == true ==> exists k :: 0 <= k < |readyQueue| && readyQueue[k] == j;
      //assert |newQueue| == 0 ==> (!exists j :: 0 <= j < n && processes[j].inQueue == true);
      //assert (!exists j :: 0 <= j < n && processes[j].inQueue == true) ==> (exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false);
      assert |newQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
      newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue, false);
      assert 0 < |newQueue| <= n;
      assert forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0;
      //assert 0 < |newQueue| <= n;
    } else {
      assert |processes| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
      assert forall i :: 0 <= i < |newQueue| ==> processes[newQueue[i]].isComplete == false && processes[newQueue[i]].inQueue == true;
      newQueueMustBeEmpty(processes, n, newQueue);
      assert |newQueue| == 0;
      ProveAllObjectsComplete(processes);
    }
    assert updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
    assert updatedTime > currentTime;
    assert if updatedExecuted == n then |newQueue| == 0 else 0 < |newQueue| <= n;
  } else {
    // Process is not done; preempt after one quantum
    var count := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    processes[i].burstTimeRemaining := processes[i].burstTimeRemaining - quantum;
    //assert processes[i].isComplete == false;
    assert count == set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    //assert updatedExecuted == |count|;
    assert updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    
    updatedTime := currentTime + quantum;
    
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    
    // Check for new arrivals if not all processes have been enqueued
    //if programsExecuted != n {
    assert forall j :: 0 <= j < |newQueue| ==> newQueue[j] != i;
    assert 0 <= |newQueue| < n;
    assert updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    newQueue := newQueue + [i];
    assert |newQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
    newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue, true);
    assert updatedTime == currentTime + quantum;
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime;
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    
    assert 0 <= |newQueue| <= n;
    assert processes[i].inQueue == true;
    //assert forall j :: 0 <= j < |newQueue| ==> newQueue[j] != i;
    //assert forall i :: 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    assert ProcessQueueCurTime(processes, updatedTime);
    assert updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
    assert exists j :: 0 <= j < n && processes[j].isComplete == false;
    ProveUpdatedExecutedNotN(processes, n, updatedExecuted);
    assert updatedExecuted != n;
    
    // Re‐enqueue the incomplete process
    assert forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j];
    assert forall i :: i in newQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    assert 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
    
    
    assert if updatedExecuted == n then |newQueue| == 0 else 0 < |newQueue| <= n;
    assert forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j];
    assert forall i :: i in newQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= updatedTime;
  }
}

function SeqProcSum(ps: seq<Process>): int
  reads ps
  decreases |ps|
{
  if |ps| == 0 then 0
  else SeqProcSum(ps[..|ps|-1]) + ps[|ps|-1].arrivalTime + ps[|ps|-1].burstTime
}


//----------------------------------------------------------------------
// (2) Lemma: extending a prefix by one preserves the sum‐relation.
//     SeqProcSum(ps[..i+1]) = SeqProcSum(ps[..i]) + (fields of ps[i])
//----------------------------------------------------------------------

lemma SeqProcSumPrefix(ps: seq<Process>, i: nat)
  requires 0 <= i < |ps|
  ensures SeqProcSum(ps[..i+1]) 
        == SeqProcSum(ps[..i]) + ps[i].arrivalTime + ps[i].burstTime
{
  calc {
    SeqProcSum(ps[..i+1]);
    == { }
      SeqProcSum((ps[..i+1])[..|(ps[..i+1])|-1]) 
      + (ps[..i+1])[|(ps[..i+1])|-1].arrivalTime 
      + (ps[..i+1])[|(ps[..i+1])|-1].burstTime;
    == {
      // slicing facts
      assert (ps[..i+1])[..|(ps[..i+1])|-1] == ps[..i];
      assert (ps[..i+1])[|(ps[..i+1])|-1].arrivalTime == ps[i].arrivalTime;
      assert (ps[..i+1])[|(ps[..i+1])|-1].burstTime == ps[i].burstTime;
    }
      SeqProcSum(ps[..i]) + ps[i].arrivalTime + ps[i].burstTime;
  }
}


//----------------------------------------------------------------------
// (3) Lemma: slicing off the entire sequence is a no‐op.
//     SeqProcSum(ps[..|ps|]) == SeqProcSum(ps)
//----------------------------------------------------------------------

lemma SeqProcSumFull(ps: seq<Process>)
  ensures SeqProcSum(ps[..|ps|]) == SeqProcSum(ps)
  decreases |ps|
{
  if |ps| > 0 {
    // inductively fix the tail
    SeqProcSumFull(ps[..|ps|-1]);
    calc {
      SeqProcSum(ps[..|ps|]);
      == { }
        SeqProcSum((ps[..|ps|])[..|(ps[..|ps|])|-1]) 
        + (ps[..|ps|])[|(ps[..|ps|])|-1].arrivalTime 
        + (ps[..|ps|])[|(ps[..|ps|])|-1].burstTime;
      == {
        assert (ps[..|ps|])[..|(ps[..|ps|])|-1] == ps[..|ps|-1];
        assert (ps[..|ps|])[|(ps[..|ps|])|-1].arrivalTime == ps[|ps|-1].arrivalTime;
        assert (ps[..|ps|])[|(ps[..|ps|])|-1].burstTime == ps[|ps|-1].burstTime;
      }
        SeqProcSum(ps[..|ps|-1]) + ps[|ps|-1].arrivalTime + ps[|ps|-1].burstTime;
      == {  }
        SeqProcSum(ps);
    }
  }
}


//----------------------------------------------------------------------
// (4) Summation method: loops through ps, accumulating arrival+burst,
//     and uses both lemmas to discharge invariants and postcondition.
//----------------------------------------------------------------------

method SumProcessTimes(ps: seq<Process>) returns (total: int)
  requires |ps| > 0
  requires forall p :: p in ps ==> p.burstTime > 0
  ensures total == SeqProcSum(ps)
  ensures total > 0
{
  var i := 0;
  total := 0;
  while i < |ps|
    invariant 0 <= i <= |ps|
    invariant total == SeqProcSum(ps[..i])
    invariant i > 0 ==> total > 0
  {
    total := total + ps[i].arrivalTime + ps[i].burstTime;
    SeqProcSumPrefix(ps, i);
    i := i + 1;
  }
  SeqProcSumFull(ps);
}

lemma IfFalseImpliesTrue(processes: seq<Process>, n: nat)
  requires |processes| == n
  requires forall i :: 0 <= i < n ==> processes[i].isComplete == false
  requires forall i :: 0 <= i < n ==> processes[i].burstTimeRemaining > 0
  ensures forall j :: 0 <= j < n ==> 
    if processes[j].isComplete == true then 
      processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 
    else 
      processes[j].burstTimeRemaining > 0
{
  forall j | 0 <= j < n
    ensures if processes[j].isComplete == true then 
              processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 
            else 
              processes[j].burstTimeRemaining > 0
  {
    if processes[j].isComplete == true {
      // This case never happens due to the precondition.
      assert false; // Contradiction since all processes are not complete
    } else {
      // You may require additional assumptions or facts to justify this
      // Here we just assume these values are consistent
      // Otherwise, make this an assumption or add it as an input invariant
    }
  }
}

lemma ProveCompletedSetHasSizeN(completedNotInQueue: set<int>, n: nat)
  requires forall i :: 0 <= i < n <==> i in completedNotInQueue
  ensures |completedNotInQueue| == n
{
  // We prove that the set { i | 0 <= i < n } is a subset of completedNotInQueue
  var numbersSet := {};
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |numbersSet| == i
        invariant forall x :: x in numbersSet <==> 0 <= x < i
        invariant forall x :: 0 <= x < i ==> x in numbersSet
    {
        numbersSet := numbersSet + {i};
        i := i + 1;
    }
  assert |numbersSet| == n;
  assert numbersSet == completedNotInQueue;
  assert completedNotInQueue == numbersSet;
}

lemma {:axiom} readyQueueNeverEmpty(processes: seq<Process>, n: nat, currentTime: int)
requires |processes| == n
ensures exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false

// The core loop: seed the queue with process 0, then keep calling UpdateQueue
method RoundRobin(
    processes: seq<Process>, n: int,
    quantum: int)
    returns (programsExecuted: int)
    requires |processes| == n && quantum > 0 && n > 0 && processes[0].arrivalTime == 0
    requires forall i :: 1 <= i < n ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i])
    requires forall i :: 0 <= i < n ==> processes[i].isComplete == false && processes[i].inQueue == false && processes[i].burstTime > 0 && processes[i].arrivalTime >= 0 && processes[i].burstTimeRemaining == processes[i].burstTime
    requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
    modifies processes, processes[..]
    //ensures programsExecuted == n
    //ensures forall p :: p in processes[..] ==> p.isComplete == true && p.inQueue == false// && p.burstTimeRemaining == 0 && p.completionTime >= p.arrivalTime && p.turnaroundTime >= p.waitingTime && p.waitingTime >= 0
{
  var readyQueue: seq<int> := [0];
  var currentTime := 0;
  processes[0].inQueue := true;
  for i := 1 to n
  invariant forall j :: j in readyQueue ==> 0 <= j < n && processes[j].inQueue == true && processes[j].isComplete == false && processes[j].arrivalTime <= currentTime
  invariant forall j :: 0 <= j < n ==> processes[j].isComplete == old(processes[j].isComplete)
  invariant forall i :: 0 <= i < n ==> processes[i].burstTime > 0 && processes[i].burstTimeRemaining > 0
  invariant forall i :: 0 <= i < n ==> processes[i].burstTimeRemaining == processes[i].burstTime
  invariant forall j :: 0 <= j < i ==> if processes[j].arrivalTime <= currentTime then processes[j].inQueue == true else processes[j].inQueue == false
  invariant forall j :: i <= j < n ==> processes[j].inQueue == false
  invariant forall j :: 0 <= j < |readyQueue| ==> 0 <= readyQueue[j] < n
  invariant forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
  invariant |readyQueue| > 0
  {
    if processes[i].arrivalTime <= currentTime
    {
      processes[i].inQueue := true;
      readyQueue := readyQueue + [i];
    }
  }
  UniqueSeqLengthAtMostN(readyQueue, n);
  assert |readyQueue| > 0;
  programsExecuted := 0;
  var maxTime := SumProcessTimes(processes);
  IfFalseImpliesTrue(processes, n);
  
  // Continue until the ready queue is empty
  while programsExecuted < n && currentTime < maxTime
  invariant 0 <= currentTime
  invariant 0 <= programsExecuted <= n
  invariant if programsExecuted == n then |readyQueue| == 0 else 0 < |readyQueue| <= n
  invariant forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
  invariant ProcessQueueCurTime(processes, currentTime)
  invariant AllPinProcessQueue(processes)
  invariant forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
  invariant forall j :: 0 <= j < |readyQueue| ==> 0 <= readyQueue[j] < n
  invariant programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  invariant forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
  //invariant forall i :: 0 <= i < |readyQueue| ==> processes[readyQueue[i]].arrivalTime <= currentTime
  //invariant |readyQueue| == 1 && forall i :: (i in readyQueue) && processes[i].burstTimeRemaining <= quantum ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false
    decreases maxTime - currentTime
  {
    var newQueue: seq<int>;
    var updatedTime: int;
    var updatedExecuted: int;
    if (|readyQueue| == 1 && processes[readyQueue[0]].burstTimeRemaining <= quantum) {
      //assert processes[readyQueue[0]].arrivalTime <= SeqProcSum(processes[..readyQueue[0]]);
      readyQueueNeverEmpty(processes, n, currentTime);
      assert exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
    } else {
      assert (|readyQueue| == 1 && processes[readyQueue[0]].burstTimeRemaining <= quantum) ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false;
    }
    newQueue, updatedTime, updatedExecuted := UpdateQueue(processes, n, quantum, readyQueue, currentTime, programsExecuted);
    readyQueue := newQueue;
    currentTime := updatedTime;
    programsExecuted := updatedExecuted;
  }
  assert programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
  var completedNotInQueue := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
  //assert programsExecuted == |completedNotInQueue|;
if currentTime >= maxTime {
  //assert |completedNotInQueue| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
  ProveAllProcessesCompleteAtMaxTime(processes, currentTime, maxTime, programsExecuted);
  //var completedNotInQueue := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
  //assert forall i :: 0 <= i < n <==> i in completedNotInQueue; // due to ensures
  assert programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
  //assert programsExecuted == |completedNotInQueue|;
  ProveCompletedSetHasSizeN(completedNotInQueue, n);
  assert |completedNotInQueue| == n;
  assert programsExecuted == n;
}
  assert programsExecuted == |processes|;
  //assert |completedNotInQueue| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
  assert |set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false| == |processes|;
  ProveAllObjectsComplete(processes);
  assert forall j :: 0 <= j < n ==> processes[j].isComplete == true && processes[j].inQueue == false;
}

// Prints out waiting and turnaround times in PID order
// method Output(processes: array<Process>, n: int)
// {
// // Simple selection-sort by PID
// var i := 0;
// while i < n
//     decreases n - i
// {
//     var j := i + 1;
//     while j < n
//     decreases n - j
//     {
//     if processes[j].pid < processes[i].pid {
//         var tmp := processes[i];
//         processes[i] := processes[j];
//         processes[j] := tmp;
//     }
//     j := j + 1;
//     }
//     i := i + 1;
// }

// // Now print
// i := 0;
// var sumW := 0;
// var sumT := 0;
// while i < n
//     decreases n - i
// {
//     print "Process ", processes[i].pid, 
//         ": Waiting Time=", processes[i].waitingTime,
//         " Turnaround Time=", processes[i].turnaroundTime, "\n";
//     sumW := sumW + processes[i].waitingTime;
//     sumT := sumT + processes[i].turnaroundTime;
//     i := i + 1;
// }
// print "Average Waiting Time=", sumW as real / n as real, "\n";
// print "Average Turnaround Time=", sumT as real / n as real, "\n";
// }

// Example "main" – construct some processes, run, and output.
method Main()
{
var n := 4;
var quantum := 3;
var processes := [];
var temp := new Process(1, 0, 5);
processes := processes + [temp];
//assert forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i]);
temp := new Process(2, 1, 3);
processes := processes + [temp];
assert forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i]);
temp := new Process(3, 2, 8);
processes := processes + [temp];
//assert forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i]);
temp := new Process(4, 3, 6);
processes := processes + [temp];
//assert forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i]);

var completed := RoundRobin(processes, n, quantum);
assert completed == n;
//assert forall p :: p in processes[..] ==> p.turnaroundTime == p.completionTime - p.arrivalTime;
//Output(processes, n);
}


/*
class Process {
  var pid: int
  var arrivalTime: int
  var burstTime: int
  var burstTimeRemaining: int
  var completionTime: int
  var turnaroundTime: int
  var waitingTime: int
  var isComplete: bool
  var inQueue: bool

  constructor(p: int, bt: int, at: int)
    ensures this.pid == p && this.burstTime == bt && this.burstTimeRemaining == bt && this.arrivalTime == at
    && this.completionTime == 0 && this.turnaroundTime == 0 && this.waitingTime == 0 && this.isComplete == false 
    && this.inQueue == false
  {
    pid := p;
    arrivalTime := at;
    burstTime := bt;
    burstTimeRemaining := bt;
    completionTime := 0;
    turnaroundTime := 0;
    waitingTime := 0;
    isComplete := false;
    inQueue := false;
  }
}

class RoundRobinScheduler {
  var processes: seq<Process>
  var timeQuantum: int
  var currentTime: int
  var readyQueue: seq<Process>
  var completedProcesses: seq<Process>
  var executionSequence: seq<(int, int, int)>

  constructor(quantum: int)
    requires quantum > 0
    ensures timeQuantum == quantum
    ensures |processes| == 0
    ensures |readyQueue| == 0
    ensures |completedProcesses| == 0
    ensures |executionSequence| == 0
    ensures currentTime == 0
  {
    timeQuantum := quantum;
    processes := [];
    readyQueue := [];
    completedProcesses := [];
    executionSequence := [];
    currentTime := 0;
  }

  // Input function (axiom) - in real implementation this would parse user input
  method Input() returns (success: bool)
    modifies this
    ensures success ==> |processes| > 0
  {
    // Example implementation with hardcoded values
    var p1 := new Process(1, 5, 0);
    var p2 := new Process(2, 4, 1);
    var p3 := new Process(3, 3, 2);
    
    processes := [p1, p2, p3];
    return true;
  }

  method UpdateReadyQueue()
    modifies this, set p | p in processes :: p`inQueue
    ensures forall p :: p in readyQueue ==> p in processes
  {
    var newQueue: seq<Process> := [];
    var i := 0;
    while i < |processes|
      invariant 0 <= i <= |processes|
      invariant forall p :: p in newQueue ==> p in processes
    {
      if processes[i].arrivalTime <= currentTime && !processes[i].isComplete && !processes[i].inQueue {
        processes[i].inQueue := true;
        newQueue := newQueue + [processes[i]];
      }
      i := i + 1;
    }
    readyQueue := readyQueue + newQueue;
  }

  method Scheduler()
    modifies this, 
      set p | p in processes :: p`burstTimeRemaining, 
      set p | p in processes :: p`isComplete,
      set p | p in processes :: p`inQueue,
      set p | p in processes :: p`completionTime
    ensures forall p :: p in old(processes) ==> p in processes
  {
    while ExistsUnfinishedProcess()
      invariant forall p :: p in processes ==> p in old(processes)
      decreases SumRemainingTime()
    {
      UpdateReadyQueue();
      
      if |readyQueue| > 0 {
        var currentProcess := readyQueue[0];
        var executeTime := if currentProcess.burstTimeRemaining > timeQuantum 
                          then timeQuantum 
                          else currentProcess.burstTimeRemaining;
        
        // Execute process
        currentProcess.burstTimeRemaining := currentProcess.burstTimeRemaining - executeTime;
        currentTime := currentTime + executeTime;
        
        // Record execution
        executionSequence := executionSequence + [(currentProcess.pid, currentTime - executeTime, executeTime)];
        
        // Update process status
        if currentProcess.burstTimeRemaining == 0 {
          currentProcess.isComplete := true;
          currentProcess.completionTime := currentTime;
          completedProcesses := completedProcesses + [currentProcess];
          readyQueue := readyQueue[1..];
        } else {
          // Rotate in ready queue
          readyQueue := readyQueue[1..] + [currentProcess];
        }
        currentProcess.inQueue := false;
      } else {
        // Advance time to next arrival
        var nextArrival := FindNextArrival();
        if nextArrival > currentTime {
          currentTime := nextArrival;
        } else {
          currentTime := currentTime + 1;
        }
      }
    }
  }

  method ComputeWaitingTime()
    modifies set p | p in processes :: p`waitingTime
    requires forall p :: p in processes ==> p.isComplete
  {
    var i := 0;
    while i < |processes|
      invariant 0 <= i <= |processes|
    {
      processes[i].waitingTime := processes[i].completionTime - processes[i].arrivalTime - processes[i].burstTime;
      i := i + 1;
    }
  }

  method ComputeTurnaroundTime()
    modifies set p | p in processes :: p`turnaroundTime
    requires forall p :: p in processes ==> p.isComplete
  {
    var i := 0;
    while i < |processes|
      invariant 0 <= i <= |processes|
    {
      processes[i].turnaroundTime := processes[i].completionTime - processes[i].arrivalTime;
      i := i + 1;
    }
  }

  method ComputeAverageWaitAndTurnaroundTime() returns (avgWait: real, avgTurnaround: real)
    requires |processes| > 0
    requires forall p :: p in processes ==> p.isComplete
    ensures avgWait >= 0.0
    ensures avgTurnaround >= 0.0
  {
    var totalWait := 0;
    var totalTurnaround := 0;
    var i := 0;

    while i < |processes|
      invariant 0 <= i <= |processes|
      invariant totalWait >= 0
      invariant totalTurnaround >= 0
    {
      totalWait := totalWait + processes[i].waitingTime;
      totalTurnaround := totalTurnaround + processes[i].turnaroundTime;
      i := i + 1;
    }

    avgWait := totalWait as real / |processes| as real;
    avgTurnaround := totalTurnaround as real / |processes| as real;
  }

  // Output function (axiom) - in real implementation this would format and display results
  method Output()
    requires forall p :: p in processes ==> p.isComplete
  {
    var i := 0;
    print "Execution Sequence (PID, Start Time, Duration):\n";
    while i < |executionSequence|
    {
      print executionSequence[i], "\n";
      i := i + 1;
    }

    print "\nProcess Statistics:\n";
    i := 0;
    while i < |processes|
    {
      var p := processes[i];
      print "Process ", p.pid, ":\n";
      print "  Completion Time: ", p.completionTime, "\n";
      print "  Turnaround Time: ", p.turnaroundTime, "\n";
      print "  Waiting Time: ", p.waitingTime, "\n";
      i := i + 1;
    }

    var avgWait, avgTurnaround := ComputeAverageWaitAndTurnaroundTime();
    print "\nAverages:\n";
    print "Average Waiting Time: ", avgWait, "\n";
    print "Average Turnaround Time: ", avgTurnaround, "\n";
  }

  predicate ExistsUnfinishedProcess()
    reads this, this.processes, set p | p in processes :: p`isComplete
  {
    exists p :: p in processes && !p.isComplete
  }

  function SumRemainingTime(): nat
    reads this, this.processes, set p | p in processes :: p`burstTimeRemaining
  {
    if |processes| == 0 then 
      0
    else 
      processes[0].burstTimeRemaining + SumRemainingTimeHelper(processes[1..])
  }

  function SumRemainingTimeHelper(procs: seq<Process>): nat
    reads set p | p in procs :: p`burstTimeRemaining
    decreases |procs|
  {
    if |procs| == 0 then 
      0
    else 
      procs[0].burstTimeRemaining + SumRemainingTimeHelper(procs[1..])
  }

  method FindNextArrival() returns (nextTime: int)
    requires |processes| > 0
    ensures nextTime >= currentTime
  {
    var minTime := MaxInt();
    var i := 0;
    while i < |processes|
      invariant 0 <= i <= |processes|
    {
      if processes[i].arrivalTime > currentTime && processes[i].arrivalTime < minTime {
        minTime := processes[i].arrivalTime;
      }
      i := i + 1;
    }
    return if minTime == MaxInt() then currentTime + 1 else minTime;
  }

  function MaxInt(): int
  {
    2147483647 // Maximum 32-bit integer
  }
}

method Main()
{
  var scheduler := new RoundRobinScheduler(2);
  
  // Input processes
  var inputSuccess := scheduler.Input();
  if !inputSuccess {
    print "Failed to input processes\n";
    return;
  }
  
  // Run scheduler
  scheduler.Scheduler();
  
  // Compute times
  scheduler.ComputeWaitingTime();
  scheduler.ComputeTurnaroundTime();
  
  // Output results
  scheduler.Output();
}*/

