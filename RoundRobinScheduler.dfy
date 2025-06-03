class Process {
var pid: int
var arrivalTime: int
var burstTime: int
var burstTimeRemaining: nat
var completionTime: int
var turnaroundTime: int
var waitingTime: int
var isComplete: bool
var inQueue: bool

constructor (id: int, arrival: int, burst: nat)
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

lemma SubsetImpliesCardinalityLe<T>(A: set<T>, B: set<T>)
  requires A <= B
  ensures  |A| <= |B|
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
    readyQueue: seq<int>)
returns (newQueue: seq<int>)
modifies processes[..]
requires |processes| == n && currentTime >= 0 && n > 0 && 0 <= |readyQueue| <= n
requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false
requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
requires forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
ensures forall i :: i in newQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false
ensures ProcessQueueCurTime(processes, currentTime)
ensures AllPinProcessQueue(processes)
ensures 0 <= |newQueue| <= n && |newQueue| >= |readyQueue|
ensures forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
ensures forall p :: (p in processes[..]) ==> old(p.inQueue) == true ==> p.inQueue == true
{
var i := 0;
newQueue := readyQueue;
while i < n
    invariant 0 <= i <= n
    invariant forall j :: j in newQueue ==> 0 <= j < n && processes[j].inQueue == true && processes[j].isComplete == false
    invariant forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
    invariant forall j :: 0 <= j < i ==> if processes[j].arrivalTime <= currentTime then (processes[j].inQueue == true || 
                processes[j].isComplete == true) else (processes[j].inQueue == false || processes[j].isComplete == false)
    invariant |newQueue| >= |readyQueue|
    invariant 0 <= |newQueue| <= n
    invariant forall i, j :: 0 <= i < j < |newQueue| ==> newQueue[i] != newQueue[j]
    invariant forall k :: 0 <= k < |newQueue| ==> 0 <= newQueue[k] < n
    invariant forall p :: (p in processes[..]) ==> old(p.inQueue) == true ==> p.inQueue == true
    decreases n - i
{
    if processes[i].arrivalTime <= currentTime
        && !processes[i].inQueue
        && !processes[i].isComplete
    {
        processes[i].inQueue := true;
        var oldLength := |newQueue|;
        newQueue := newQueue + [i];
    }
    UniqueSeqLengthAtMostN(newQueue, n);
    i := i + 1;
}
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
    requires forall i :: i in readyQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false
    requires ProcessQueueCurTime(processes, currentTime)
    requires AllPinProcessQueue(processes)
    requires forall i, j :: 0 <= i < j < |readyQueue| ==> readyQueue[i] != readyQueue[j]
    requires forall k :: 0 <= k < |readyQueue| ==> 0 <= readyQueue[k] < n
    requires forall p :: (p in processes[..]) ==> (p.inQueue == false || p.isComplete == false)
    
    ensures forall i :: i in newQueue ==> 0 <= i < n && processes[i].inQueue == true && processes[i].isComplete == false
    //ensures InQueue(processes, updatedTime)
    //ensures 0 <= |newQueue| <= n
    //ensures updatedTime > currentTime
    ensures updatedExecuted >= programsExecuted
    //ensures forall p :: p in processes[..] ==> p.isComplete == true && p.inQueue == false && p.burstTimeRemaining == 0 && p.completionTime >= p.arrivalTime && p.turnaroundTime >= p.waitingTime && p.waitingTime >= 0
{
  // Initialize return values
  newQueue := readyQueue;
  updatedTime := currentTime;
  updatedExecuted := programsExecuted;
  
  // Pop the first index off the ready queue
  var i := newQueue[0];
  newQueue := newQueue[1..];
  if processes[i].burstTimeRemaining <= quantum {
    // Process will finish in this quantum
    assert  !exists j :: 0 <= j < |newQueue| && newQueue[j] == i;
    assert ProcessQueueCurTime(processes, updatedTime);
    assert AllPinProcessQueue(processes);
    processes[i].isComplete := true;
    assert  !exists j :: 0 <= j < |newQueue| && newQueue[j] == i;
    assert ProcessQueueCurTime(processes, updatedTime);
    assert AllPinProcessQueue(processes);
    updatedTime := currentTime + processes[i].burstTimeRemaining;
    processes[i].completionTime := updatedTime;
    processes[i].waitingTime := processes[i].completionTime - processes[i].arrivalTime - processes[i].burstTime;
    processes[i].turnaroundTime := processes[i].waitingTime + processes[i].burstTime;
    if processes[i].waitingTime < 0 {
      processes[i].waitingTime := 0;
    }
    processes[i].burstTimeRemaining := 0;
    updatedExecuted := programsExecuted + 1;

    // Check for new arrivals if not all processes have been enqueued
    if updatedExecuted != n {
      newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue);
      assert forall p :: (p in processes[..]) ==> if p.arrivalTime <= currentTime then (p.inQueue == true || p.isComplete == true) else (p.inQueue == false || p.isComplete == false);
    }
  } else {
    // Process is not done; preempt after one quantum
    processes[i].burstTimeRemaining := processes[i].burstTimeRemaining - quantum;
    updatedTime := currentTime + quantum;

    // Check for new arrivals if not all processes have been enqueued
    if programsExecuted != n {
      newQueue := CheckForNewArrivals(processes, n, updatedTime, newQueue);
    }
    // Re‐enqueue the incomplete process
    newQueue := newQueue + [i];
  }
}

// The core loop: seed the queue with process 0, then keep calling UpdateQueue
method RoundRobin(
    processes: seq<Process>, n: int,
    quantum: int)
    returns (programsExecuted: int)
    requires |processes| == n && quantum > 0 && n > 0
    //modifies processes, processes[..]
    ensures programsExecuted == n
    ensures forall p :: p in processes[..] ==> p.isComplete == true && p.inQueue == false && p.burstTimeRemaining == 0 && p.completionTime >= p.arrivalTime && p.turnaroundTime >= p.waitingTime && p.waitingTime >= 0
{
var readyQueue := [];
var currentTime := 0;
programsExecuted := 0;
while programsExecuted < n
    invariant 0 <= |readyQueue| <= n
    invariant forall i :: i in readyQueue ==> 0 <= i < n
    invariant forall i :: i in readyQueue ==> processes[i].inQueue == true && processes[i].isComplete == false
    decreases n - programsExecuted
{
    var q: seq<int>;
    var ct: int;
    var pe: int;
    q, ct, pe := UpdateQueue(processes, n, quantum, readyQueue, currentTime, programsExecuted);
    readyQueue := q;
    currentTime := ct;
    programsExecuted := pe;
}
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
temp := new Process(2, 1, 3);
processes := processes + [temp];
temp := new Process(3, 2, 8);
processes := processes + [temp];
temp := new Process(4, 3, 6);
processes := processes + [temp];

var completed := RoundRobin(processes, n, quantum);
assert completed == n;
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

