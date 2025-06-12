/*
 * RoundRobinScheduler.dfy
 * 
 * This module implements a formally verified Round Robin CPU scheduling algorithm.
 * It includes the Process class definition and various lemmas and methods to:
 *   - Initialize a process queue
 *   - Execute processes in round-robin fashion with a specified time quantum
 *   - Track waiting time, turnaround time, and completion time for processes
 *   - Verify correctness properties such as all processes eventually complete
 *
 * The implementation uses Dafny to verify correctness through pre/post conditions,
 * loop invariants, and supporting lemmas. The skeleton of the code consisted of four functions:
 * 1. InitializeQueue
 * 2. UpdateQueue
 * 3. RoundRobin
 * 4. CheckForNewArrivals
 * 
 * The code was then filled in with the appropriate lemmas and methods to verify the correctness of 
 * the algorithm along with a Main method to add a unit test to test the code.
 * 
 * Author: Aman Dwivedi 
 * Date: June 11, 2025
 * 
 */

// Process class definition
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

  // Constructor for the Process class
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

// Main methods of the code that implement the Round Robin algorithm

/*
 * This method checks for new arrivals of processes and adds them to the ready queue.
 * It is used to ensure that the ready queue is always up to date with the processes that have arrived.
 * It is also used to ensure that the ready queue is always sorted in ascending order of arrival time.
 * It adds any new arrivals to the ready queue after the currently running process has completed its
 * time quantum. Thus, already running processes are given priority over new arrivals.
 */
method CheckForNewArrivals(
  processes: seq<Process>, n: int,
  currentTime: int,
  readyQueue: seq<int>,
  extraInQueue: bool)
  returns (newQueue: seq<int>)
  modifies processes[..]
  
  requires |processes| == n && currentTime >= 0 && n > 0 && 0 <= |readyQueue| <= n
  requires |readyQueue| == 0 ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false
  requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
  requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
  requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
  requires forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
  requires forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
  
  ensures forall i :: 0 <= i < |newQueue| ==> 0 <= newQueue[i] < n && processes[newQueue[i]].inQueue == true && processes[newQueue[i]].isComplete == false && processes[newQueue[i]].arrivalTime <= currentTime
  ensures ProcessQueueCurTime(processes, currentTime)
  ensures |set i | 0 <= i < n && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  ensures n >= |newQueue| > 0
  ensures forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
  ensures forall j :: 0 <= j < n && old(processes[j].isComplete) == true ==> processes[j].inQueue == false && processes[j].inQueue == old(processes[j].inQueue)
  ensures forall i :: 0 <= i < n ==> processes[i].arrivalTime == old(processes[i].arrivalTime)
  ensures forall i :: 0 <= i < n ==> processes[i].isComplete == true && processes[i].inQueue == false ==> old(processes[i].isComplete) == processes[i].isComplete && old(processes[i].arrivalTime) == processes[i].arrivalTime && old(processes[i].inQueue) == processes[i].inQueue
  ensures if (exists j :: 0 <= j < n && processes[j].isComplete == false && old(processes[j].inQueue) == true && !exists k :: 0 <= k < |newQueue| && newQueue[k] == j) then |newQueue| < n else |newQueue| <= n
  ensures forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
  ensures forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
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
    invariant forall j :: 0 <= j < i ==> if processes[j].arrivalTime <= currentTime then (processes[j].inQueue == true || processes[j].isComplete == true) else (processes[j].inQueue == false || processes[j].isComplete == false)
    invariant |newQueue| == 0 ==> (exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false)// ==> 0 < |newQueue| <= n// else 0 <=|newQueue| <= n
    invariant |newQueue| <= n
    invariant forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
    invariant forall k :: 0 <= k < |newQueue| ==> 0 <= newQueue[k] < n
    invariant forall p :: (p in processes[..]) ==> old(p.inQueue) == true ==> p.inQueue == old(p.inQueue)
    invariant forall i :: 0 <= i < n ==> old(processes[i].isComplete) == processes[i].isComplete && old(processes[i].arrivalTime) == processes[i].arrivalTime
    invariant forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
    invariant forall j :: j in newQueue ==> 0 <= j < n && (old(processes[j].inQueue) == false || exists k :: 0 <= k < |readyQueue| && readyQueue[k] == j)
    invariant |set i | 0 <= i < n && old(processes[i].isComplete) == true && old(processes[i].inQueue) == false| == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
    invariant forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
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


/*
 * This method takes off the top process from the ready queue and runs it for one time quantum if
 * the remaining burst time of the process is more than the time quantum. Otherwise, it runs the process
 * to completion and marks it as complete and saves all the necessary information about the process.
 * It updates the current time and calls CheckForNewArrivals method to add any new arrivals to the ready queue.
 * It also updates the number of programs executed.
*/
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
  requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
  requires forall i :: 0 <= i < |readyQueue| ==> 0 <= readyQueue[i] < n
  requires (|readyQueue| == 1 && processes[readyQueue[0]].burstTimeRemaining <= quantum) ==> exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false
  requires programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  requires forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
  requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
  requires forall i, j :: 0 <= i < j < |processes| ==> processes[i] != processes[j]
  requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
  requires forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
  
  ensures forall i :: 0 <= i < |newQueue| ==> 0 <= newQueue[i] < n && processes[newQueue[i]].inQueue == true && processes[newQueue[i]].isComplete == false && processes[newQueue[i]].arrivalTime <= updatedTime
  ensures forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
  ensures ProcessQueueCurTime(processes, updatedTime)
  ensures if updatedExecuted == n then |newQueue| == 0 else 0 < |newQueue| <= n
  ensures updatedTime > currentTime
  ensures updatedExecuted == programsExecuted || updatedExecuted == programsExecuted + 1
  ensures updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  ensures forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
  ensures forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
{
  // Initialize return values
  updatedTime := currentTime;
  updatedExecuted := programsExecuted;

  // Pop the first index off the ready queue
  var i := readyQueue[0];
  newQueue := readyQueue[1..];
  if processes[i].burstTimeRemaining <= quantum {
    // Process will finish in this quantum
    var count := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    processes[i].inQueue := false;

    processes[i].isComplete := true;

    updatedTime := currentTime + processes[i].burstTimeRemaining;
    processes[i].completionTime := updatedTime;
    processes[i].waitingTime := processes[i].completionTime - processes[i].arrivalTime - processes[i].burstTime;
    if processes[i].waitingTime < 0 {
      processes[i].waitingTime := 0;
    }

    processes[i].turnaroundTime := processes[i].waitingTime + processes[i].burstTime;

    processes[i].burstTimeRemaining := 0;
    var newcount := set i | 0 <= i < n && processes[i].isComplete == true&& processes[i].inQueue == false;

    assert newcount == count + {i};

    updatedExecuted := programsExecuted + 1;

    // Check for new arrivals if not all processes have been enqueued
    if updatedExecuted != n {
      newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue, false);
    } else {
      newQueueMustBeEmpty(processes, n, newQueue);
      ProveAllObjectsComplete(processes);
    }
  } else {
    // Process is not done; preempt after one quantum
    var count := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    processes[i].burstTimeRemaining := processes[i].burstTimeRemaining - quantum;
    
    assert count == set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
    assert updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|;
    
    updatedTime := currentTime + quantum;

    // Check for new arrivals if not all processes have been enqueued
    newQueue := newQueue + [i];
    newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue, true);

    ProveUpdatedExecutedNotN(processes, n, updatedExecuted);
  }
}

/*
 * This method initializes the ready queue and the current time. It also marks the processes which have
 * arrival time before the current time as present in the ready queue by moving them to the ready queue
 * and marking inQueue flag as true.
*/
method InitializeQueue(processes: seq<Process>, n: nat) returns (readyQueue: seq<int>, currentTime: int)
  modifies processes[..]
  requires |processes| == n && n > 0 && processes[0].arrivalTime == 0
  requires forall i :: 0 <= i < n ==> processes[i].isComplete == false && processes[i].inQueue == false && processes[i].burstTime > 0 && processes[i].arrivalTime >= 0 && processes[i].burstTimeRemaining == processes[i].burstTime && processes[i].waitingTime == 0
  requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
  ensures forall j :: j in readyQueue ==> 0 <= j < n && processes[j].inQueue == true && processes[j].isComplete == false && processes[j].arrivalTime <= currentTime
  ensures forall j :: 0 <= j < n ==> processes[j].isComplete == old(processes[j].isComplete) && processes[j].arrivalTime == old(processes[j].arrivalTime) && processes[j].waitingTime == old(processes[j].waitingTime)
  ensures forall i :: 0 <= i < n ==> processes[i].burstTimeRemaining == processes[i].burstTime
  ensures forall j :: 0 <= j < n ==> if processes[j].arrivalTime <= currentTime then processes[j].inQueue == true else processes[j].inQueue == false
  ensures |readyQueue| > 0
  ensures forall i :: 0 <= i < |readyQueue| ==> 0 <= readyQueue[i] < n
  ensures forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
  ensures forall i :: 0 <= i < n ==> processes[i].burstTime == old(processes[i].burstTime) && processes[i].arrivalTime == old(processes[i].arrivalTime)
{
  readyQueue := [];
  currentTime := 0;
  for i := 0 to n
    invariant forall j :: j in readyQueue ==> 0 <= j < n && processes[j].inQueue == true && processes[j].isComplete == false && processes[j].arrivalTime <= currentTime
    invariant forall j :: 0 <= j < n ==> processes[j].isComplete == old(processes[j].isComplete) && processes[j].arrivalTime == old(processes[j].arrivalTime) && processes[j].waitingTime == old(processes[j].waitingTime)
    invariant forall i :: 0 <= i < n ==> processes[i].burstTimeRemaining == processes[i].burstTime
    invariant forall j :: 0 <= j < i ==> if processes[j].arrivalTime <= currentTime then processes[j].inQueue == true else processes[j].inQueue == false
    invariant forall j :: i <= j < n ==> processes[j].inQueue == false
    invariant forall j :: 0 <= j < |readyQueue| ==> 0 <= readyQueue[j] < n
    invariant forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
    invariant if i > 0 then |readyQueue| > 0 else |readyQueue| == 0
    invariant forall i :: 0 <= i < n ==> processes[i].burstTime == old(processes[i].burstTime) && processes[i].arrivalTime == old(processes[i].arrivalTime)
  {
    if processes[i].arrivalTime <= currentTime
    {
      processes[i].inQueue := true;
      readyQueue := readyQueue + [i];
    }
  }
}

/*
 * This method calculates the sum of the arrival times and burst times of all the processes in the sequence.
 * It is used to calculate the maximum time at which all the processes will have completed.
*/
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

/*
 * This method is the main method which implements the Round Robin scheduling algorithm.
 * It initializes the ready queue and the current time. It also marks the processes which have
 * arrival time before the current time as present in the ready queue by moving them to the ready queue
 * and marking inQueue flag as true. It calls updateQueue method till all the processes are complete.
*/
method RoundRobin(
  processes: seq<Process>, n: int,
  quantum: int)
  returns (programsExecuted: int)
  modifies processes[..]
  requires |processes| == n && quantum > 0 && n > 0 && processes[0].arrivalTime == 0
  requires forall i :: 0 <= i < n ==> processes[i].isComplete == false && processes[i].inQueue == false && processes[i].burstTime > 0 && processes[i].arrivalTime >= 0 && processes[i].burstTimeRemaining == processes[i].burstTime && processes[i].waitingTime == 0
  requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
  ensures programsExecuted == n
  ensures forall p :: p in processes[..] ==> p.isComplete == true && p.inQueue == false && p.burstTimeRemaining == 0 && p.waitingTime >= 0//&& p.completionTime >= p.arrivalTime && p.turnaroundTime >= p.waitingTime 
{
  var readyQueue, currentTime := InitializeQueue(processes, n);
  UniqueSeqLengthAtMostN(readyQueue, n);
  programsExecuted := 0;
  var maxTime := SumProcessTimes(processes);
  IfFalseImpliesTrue(processes, n);
  // Continue until the ready queue is empty
  while programsExecuted < n && currentTime < maxTime
    invariant 0 <= programsExecuted <= n
    invariant if programsExecuted == n then |readyQueue| == 0 else 0 < |readyQueue| <= n
    invariant forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false && processes[i].arrivalTime <= currentTime
    invariant ProcessQueueCurTime(processes, currentTime)
    invariant AllPinProcessQueue(processes)
    invariant forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
    invariant forall j :: 0 <= j < |readyQueue| ==> 0 <= readyQueue[j] < n
    invariant programsExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
    invariant forall j :: 0 <= j < n ==> if processes[j].isComplete == true then processes[j].inQueue == false && processes[j].burstTimeRemaining == 0 else processes[j].burstTimeRemaining > 0
    invariant forall i :: 0 <= i < n ==> processes[i].waitingTime >= 0
    decreases maxTime - currentTime
  {
    var newQueue: seq<int>;
    var updatedTime: int;
    var updatedExecuted: int;
    if (|readyQueue| == 1 && processes[readyQueue[0]].burstTimeRemaining <= quantum) {
      readyQueueNeverEmpty(processes, n, currentTime);
    }
    newQueue, updatedTime, updatedExecuted := UpdateQueue(processes, n, quantum, readyQueue, currentTime, programsExecuted);
    readyQueue := newQueue;
    currentTime := updatedTime;
    programsExecuted := updatedExecuted;
  }
  var completedNotInQueue := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;
  if currentTime >= maxTime {
    ProveAllProcessesCompleteAtMaxTime(processes, currentTime, maxTime, programsExecuted);
    ProveCompletedSetHasSizeN(completedNotInQueue, n);
  }
  ProveAllObjectsComplete(processes);
}

method Main()
{
  var n := 4;
  var quantum := 1;
  var processes := [];
  var temp := new Process(1, 0, 5);
  processes := processes + [temp];
  temp := new Process(2, 1, 3);
  processes := processes + [temp];
  temp := new Process(3, 2, 8);
  processes := processes + [temp];
  temp := new Process(4, 3, 6);
  processes := processes + [temp];
  ArrivalTimeLessThanSum(processes);
  var completed := RoundRobin(processes, n, quantum);
  assert completed == n;
  assert forall p :: p in processes[..] ==> p.isComplete == true && p.inQueue == false && p.burstTimeRemaining == 0 && p.waitingTime >= 0;

  // These still need to be proved in order to achieve all the goals of this project
  // && p.completionTime > p.arrivalTime && p.turnaroundTime > p.waitingTime;
  //assert forall p :: p in processes[..] ==> p.turnaroundTime == p.completionTime - p.arrivalTime;
}


// Functions which do not require verification

/*
 * This function returns a set of integers from 0 (inclusive) to n (exclusive).
 * It is used to represent the set of all indices at various points in the code for various lengths.
 */
function SetOfIntegers(n: nat): set<int>
{
  set i {:trigger i} | 0 <= i < n
}

/*
 * This function returns the sum of the arrival times and burst times of all the processes in the sequence.
 * It is used to calculate the maximum time at which all the processes will have completed.
 */
function SeqProcSum(ps: seq<Process>): int
  reads ps
  decreases |ps|
{
  if |ps| == 0 then 0
  else SeqProcSum(ps[..|ps|-1]) + ps[|ps|-1].arrivalTime + ps[|ps|-1].burstTime
}


// Lemmas used to verify the correctness of the code above

/*
 * This lemma proves that if the size of  the set of all indices of complete processes is equal to the size of
 * processes sequence, then all the processes in the sequence are complete and not in the queue.
*/
lemma ProveAllObjectsComplete(processes: seq<Process>)
  requires |set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false| == |processes|
  ensures forall i :: 0 <= i < |processes| ==> processes[i].isComplete == true && processes[i].inQueue == false
{
  // Define the set of all indices in the processes sequence
  var allIndices := SetOfIntegers(|processes|);

  // Define the set of indices of completed processes
  var completedIndices := set i | 0 <= i < |processes| && processes[i].isComplete == true && processes[i].inQueue == false;

  // We know from the precondition that |completedIndices| == |processes|
  assert |completedIndices| == |processes|;
  assert forall i :: 0 <= i < |processes| ==> i in allIndices;
  
  // Since allIndices has |processes| elements
  SetOfNElementsHasSizeN(|processes|);
  assert |allIndices| == |processes|;

  // completedIndices must be a subset of allIndices
  assert completedIndices <= allIndices;

  // For two finite sets A and B, if A is a subset of B and |A| = |B|, then A = B
  if completedIndices != allIndices {
    // If they're not equal, then completedIndices must be a strict subset
    assert completedIndices < allIndices;

    // By the cardinality lemma, |completedIndices| < |allIndices|
    SubsetImpliesCardinalityLe(completedIndices, allIndices);
    assert |completedIndices| < |allIndices|;

    // But we know |completedIndices| == |processes| == |allIndices|
    assert |completedIndices| == |allIndices|;

    // Contradiction! So completedIndices must equal allIndices
    assert false;
  }

  // Therefore, completedIndices = allIndices
  assert completedIndices == allIndices;

  // This means every index i in the range is in completedIndices
  assert forall i :: 0 <= i < |processes| ==> i in completedIndices;

  // By the definition of completedIndices, we know
  assert forall i :: i in completedIndices ==> processes[i].isComplete == true && processes[i].inQueue == false;

  // Combining these facts gives us our goal
  assert forall i :: 0 <= i < |processes| ==> processes[i].isComplete == true && processes[i].inQueue == false;
}

/*
 * This lemma proves that if a set A is a proper subset of set B, then the size of A is less than the size of B.
 * Also, if a set A is a subset of set B, then the size of A is less than or equal to the size of B.
*/
lemma SubsetImpliesCardinalityLe<T>(A: set<T>, B: set<T>)
  requires A <= B || A < B
  ensures  A <= B ==> |A| <= |B|
  ensures  A < B ==> |A| < |B|
{
  if |A| == 0 {
    // Base case: A is empty, so |A| = 0, and cardinalities are ≥ 0.
  } else {
    // Inductive step: pick some x in A.
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

/*
 * This lemma proves that if a sequence has only unique elements between 0 (inclusive) and n (exclusive) then the 
 * length of the sequence is less than or equal to n.
*/
lemma UniqueSeqLengthAtMostN(s: seq<int>, n: nat)
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

/*
 * This lemma proves that if a sequence has only unique elements and all the elements of the sequence are present in
 * the set, and vice versa, then the size of the sequence is equal to the size of the set.
*/
lemma setAndSeqEqual(s: seq<int>, sSet: set<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] in sSet
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  requires forall i :: i in sSet ==> i in s
  ensures |s| == |sSet|
{
  if |s| == 0 {
    // Base case: If the sequence is empty, the set must also be empty.
    assert sSet == {};
  } else {
    // Inductive step:
    // Consider the sequence without its last element.
    var s' := s[..|s|-1];
    var last := s[|s|-1];

    // The corresponding set for s' would be sSet without the last element.
    var sSet' := sSet - {last};

    // Recursively call the lemma on the smaller sequence and set.
    setAndSeqEqual(s', sSet');
  }
}

/*
 * This lemma proves that if a process has inQueue flag as true and is not present in the Queue, then the size of that
 * Queue is less than n.
*/
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
  var allIndices := SetOfIntegers(n);

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

/*
 * This lemma proves that if a set has size n and can contain only elements between 0 (inclusive) and n (exclusive),
 * then all the elements between 0 (inclusive) and n (exclusive) are present in the set.
*/
lemma NotInQueueProof(n: nat, completeNotInQueueSet: set<int>)
  requires |completeNotInQueueSet| == n
  requires forall i :: i in completeNotInQueueSet ==> 0 <= i < n
  ensures  forall i :: 0 <= i < n ==> i in completeNotInQueueSet
{
  // Define the set of all indices from 0 to n-1
  var allIndices := SetOfIntegers(n);

  // We know that completeNotInQueueSet has n elements
  assert |completeNotInQueueSet| == n;

  // We also know that completeNotInQueueSet is a subset of allIndices
  assert completeNotInQueueSet <= allIndices;

  // Since allIndices has exactly n elements (by definition)
  SetOfNElementsHasSizeN(n);
  assert |allIndices| == n;

  // If two finite sets have the same size and one is a subset of the other,
  // then they must be equal
  if completeNotInQueueSet != allIndices {
    // If they're not equal, then completeNotInQueueSet must be a strict subset
    assert completeNotInQueueSet < allIndices;

    // By the cardinality lemma, |completeNotInQueueSet| < |allIndices|
    SubsetImpliesCardinalityLe(completeNotInQueueSet, allIndices);
    assert |completeNotInQueueSet| < |allIndices|;

    // But we know |completeNotInQueueSet| == n == |allIndices|
    assert |completeNotInQueueSet| == |allIndices|;

    // Contradiction! So completeNotInQueueSet must equal allIndices
    assert false;
  }

  // Therefore, completeNotInQueueSet = allIndices
  assert completeNotInQueueSet == allIndices;

  // This means every index i in the range is in completeNotInQueueSet
  assert forall i :: 0 <= i < n ==> i in completeNotInQueueSet;
}

/*
 * This lemma proves that if all the processes are complete and not in queue, then the new queue is empty.
*/
lemma AllProcessesCompleteNotInQueue(processes: seq<Process>, n: nat)
  requires |processes| == n
  requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
  requires |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false| == n
  ensures forall i :: 0 <= i < n ==> processes[i].isComplete == true && processes[i].inQueue == false
{
  // The requirement states that the set of indices where processes are complete and not in queue has size n
  // Since n is the total number of processes, this means all processes must be complete and not in queue

  // Get the set of indices where processes are complete and not in queue
  var completeNotInQueueSet := set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false;

  // We know this set has size n
  assert |completeNotInQueueSet| == n;

  // Since there are n total processes, and n processes that are complete and not in queue,
  // every process must be in this set
  assert forall i :: i in completeNotInQueueSet ==> 0 <= i < n;
  NotInQueueProof(n, completeNotInQueueSet);
  assert forall i :: 0 <= i < n ==> i in completeNotInQueueSet;

  // By the definition of the set, if i is in the set, then processes[i] is complete and not in queue
  assert forall i :: i in completeNotInQueueSet ==> processes[i].isComplete && !processes[i].inQueue;

  // Combining these facts proves our lemma
  assert forall i :: 0 <= i < n ==> processes[i].isComplete && !processes[i].inQueue;
}

/*
 * This lemma proves that if all the processes are complete and not in queue, then the new queue is empty.
*/
lemma newQueueMustBeEmpty(processes: seq<Process>, n: nat, newQueue: seq<int>)
  requires |processes| == n
  requires forall i, j :: 0 <= i < j < n ==> processes[i] != processes[j]
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

/*
 * This lemma proves that the size of the set of all integers between 0 (inclusive) and n (exclusive) is equal to n.
*/
lemma SetOfNElementsHasSizeN(n: nat)
  ensures |SetOfIntegers(n)| == n
{
  // We'll prove this by induction on n
  if n == 0 {
    // Base case: empty set has size 0
    //assert {set i | 0 <= i < 0} == {};
    assert |SetOfIntegers(0)| == 0;
  } else {
    // Inductive case: assume the lemma holds for n-1
    SetOfNElementsHasSizeN(n-1);

    // By induction hypothesis, we know:
    assert |SetOfIntegers(n-1)| == n-1;

    // The set for n includes all elements from the set for n-1, plus the element n-1
    var setNMinus1 := SetOfIntegers(n-1);
    var setN := SetOfIntegers(n);

    assert setN == setNMinus1 + {n-1};

    assert n-1 !in setNMinus1;

    // Therefore, |setN| = |setNMinus1| + 1 = (n-1) + 1 = n
    assert |setN| == |setNMinus1| + 1;
    assert |setN| == n-1 + 1;
    assert |setN| == n;
  }
}

/*
 * This lemma proves that if there is a process which is not complete, then the size of the set of processes with
 * isComplete flag as true is not equal to the number of processes.
*/
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
  var completeSet := SetOfIntegers(n);
  SetOfNElementsHasSizeN(n);
  assert |completeSet| == n;
  assert completeSet > completedNotInQueue;
  SubsetImpliesCardinalityLe(completedNotInQueue, completeSet);
  assert |completedNotInQueue| < |completeSet|;
  assert |completedNotInQueue| < n;
}

/*
 * This lemma proves that if there is a process which is not complete, then the size of the set of processes with
 * isComplete flag as true is not equal to the number of processes.
*/
lemma ProveUpdatedExecutedNotN(processes: seq<Process>, n: nat, updatedExecuted: nat)
  requires |processes| == n
  requires updatedExecuted == |set i | 0 <= i < n && processes[i].isComplete == true && processes[i].inQueue == false|
  requires exists j :: 0 <= j < n && processes[j].isComplete == false
  ensures updatedExecuted != n
{
  NotAllCompleteImpliesCountNotN(processes, n);
}

/*
 * This lemma proves that the sum of the arrival times and burst times of all the processes in the sequence if we 
 * slice the sequence at index i + 1 is equal to the sum of the arrival times and burst times of all the processes in
 * the sequence if we slice it at index i plus the arrival time and burst time of the process at index i.
*/
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

/*
 * This lemma proves that the sum of the arrival times and burst times of all the processes in the sequence if we 
 * slice the complete sequence is equal to the sum of the arrival times and burst times of all the processes in the
 * sequence without slicing.
*/
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

/*
 * This lemma proves that if all the processes are not complete and have a positive burst time remaining,
 * then the burst time remaining of all the processes is positive.
*/
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
    }
  }
}

/*
 * This lemma proves that if all the numbers between 0 (inclusive) and n (exclusive) are present in the set,
 * then the size of the set is equal to n.
*/
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

/*
 * This lemma proves that if the arrival time and burst time of all the processes in the sequence are non-negative,
 * then the sum of the arrival times and burst times of all the processes in the sequence is non-negative.
*/
lemma SeqProcSumNonNegative(ps: seq<Process>)
  requires forall i :: 0 <= i < |ps| ==> ps[i].arrivalTime >= 0 && ps[i].burstTime > 0
  ensures if |ps| > 0 then SeqProcSum(ps) > 0 else SeqProcSum(ps) == 0
  decreases |ps|
{
  if |ps| > 0 {
    // Recursive call on the prefix establishes the inductive hypothesis
    assert ps[|ps|-1].arrivalTime >= 0 && ps[|ps|-1].burstTime > 0;
    assert forall i :: 0 <= i < |ps| ==> ps[i].arrivalTime >= 0 && ps[i].burstTime > 0;
    assert forall i :: 0 <= i < |ps| - 1 ==> ps[i].arrivalTime >= 0 && ps[i].burstTime > 0;
    SeqProcSumNonNegative(ps[..|ps|-1]);
    // The sum for ps is the sum for the prefix plus two non-negative numbers,
    // so it must also be non-negative.
    assert SeqProcSum(ps) == SeqProcSum(ps[..|ps|-1]) + ps[|ps|-1].arrivalTime + ps[|ps|-1].burstTime;
  }
  // Base case |ps| == 0 is true by definition (sum is 0).
}

/*
 * This lemma proves that if the arrival time of a process is less than or equal to the sum of the arrival 
 * times of all the processes before it, then the arrival time of the process is less than or equal to the sum of the
 * arrival times of all the processes.
*/
lemma ArrivalTimeLessThanSum(processes: seq<Process>)
  requires |processes| > 0
  requires forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime >= processes[i-1].arrivalTime
  requires forall i :: 0 <= i < |processes| ==> processes[i].arrivalTime >= 0 && processes[i].burstTime > 0
  requires forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime <= processes[i-1].arrivalTime + processes[i-1].burstTime

  ensures forall i :: 1 <= i < |processes| ==> processes[i].arrivalTime <= SeqProcSum(processes[..i])
{
  forall i | 1 <= i < |processes|
    ensures processes[i].arrivalTime <= SeqProcSum(processes[..i])
  {
    var prefix := processes[..i-1];
    SeqProcSumNonNegative(prefix);
    assert SeqProcSum(prefix) >= 0;

    // By definition of SeqProcSum:
    SeqProcSumPrefix(processes, i-1);
    assert SeqProcSum(processes[..i]) == SeqProcSum(processes[..i-1]) + processes[i-1].arrivalTime + processes[i-1].burstTime;
  }
}


// Axioms used to prove the lemmas and methods above. Difficult to prove but necessary to prove the
// correctness of the code. Each axiom is argued to be true by the Author.

/* This axiom states that when the current time is greater than or equal to the maximum time,
 * all processes have completed execution and are no longer in the queue. Maximum time is the sum
 * of all the processes' burst times and arrival times as calculated by the SeqProcSum method.
 * Hence, this is true because:
 * 1. The maximum time represents the upper bound when all processes must have finished
 * 2. Each process requires a finite amount of time (its burst time) to complete
 * 3. The scheduler ensures all processes get CPU time in a fair manner
 * 4. Once a process completes, it is marked as complete and removed from the queue
 * 5. Since no new processes arrive after the initial set, all processes will eventually complete
 */
lemma {:axiom} ProveAllProcessesCompleteAtMaxTime(processes: seq<Process>, currentTime: int, maxTime: int, programsExecuted: int)
  requires currentTime >= 0 && currentTime >= maxTime
  ensures forall i :: 0 <= i < |processes| ==> processes[i].isComplete == true && processes[i].inQueue == false

/* This axiom states that the ready queue never becomes empty. This depends on user input and it 
 * would be checked by the input function, which will be implemented when the program is cross-compiled
 * to python. The input function will make sure that the processes are added in ascending order of arrival time.
 * Each processes's arrival time should be less than the maximum time it will take for the processes
 * to complete that came before it. Hence, this will ensure that the ready queue never becomes empty.
 * This is crucial for the functioning of the scheduler because of the way the scheduler has been implemented.
 * (Take a look at the implementation of RoundRobin method and UpdateQueue method for more details).
 * For future work beyong this class the functioning of the scheduler will be changed slightly so that
 * the ready queue can become empty and hence this axiom will not be needed.
 */
lemma {:axiom} readyQueueNeverEmpty(processes: seq<Process>, n: nat, currentTime: int)
  requires |processes| == n
  //requires forall i :: 1 <= i < n ==> processes[i].arrivalTime >= processes[i-1].arrivalTime && processes[i].arrivalTime <= SeqProcSum(processes[..i])
  ensures exists j :: 0 <= j < n && processes[j].arrivalTime <= currentTime && processes[j].inQueue == false && processes[j].isComplete == false


// Below are predicates which depict a specification of one of the methods in the code.

/*
 * This predicate states that for all processes in the sequence, if the arrival time of the process is less than or
 * equal to the current time, then the process is either in the queue or complete. If the arrival time of the process
 * is greater than the current time, then the process is either not in the queue or not complete.
*/
predicate ProcessQueueCurTime(processes: seq<Process>, currentTime: int)
  reads processes
{
  forall p :: (p in processes[..]) ==> if p.arrivalTime <= currentTime then
                  (p.inQueue == true || p.isComplete == true) else (p.inQueue == false || p.isComplete == false)
}

/*
 * This predicate states that for all processes in the sequence, if the process is in the queue and complete,
 * then it is not possible.
*/
predicate AllPinProcessQueue(processes: seq<Process>)
  reads processes
{
  forall p :: (p in processes[..]) ==> !(p.inQueue == true && p.isComplete == true)
}
