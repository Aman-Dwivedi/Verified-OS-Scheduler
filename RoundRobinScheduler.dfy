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

constructor (id: int, arrival: int, burst: int)
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

// Scans all processes and enqueues any that have arrived but are not yet in the queue
method CheckForNewArrivals(
    processes: array<Process>, n: int,
    currentTime: int,
    readyQueue: seq<int>)
returns (newQueue: seq<int>)
modifies processes[..]
requires processes.Length == n && currentTime >= 0 && n > 0
requires forall i :: i in readyQueue ==> 0 <= i < n
requires forall i :: i in readyQueue ==> processes[i].inQueue == true && processes[i].isComplete == false
ensures forall i :: i in readyQueue ==> processes[i].inQueue == true && processes[i].isComplete == false
//ensures forall p :: (p in processes[..] && p.arrivalTime > currentTime) ==> (p.inQueue == false && p.isComplete == false) 
{
newQueue := readyQueue;
var i := 0;
while i < processes.Length
    invariant 0 <= i <= processes.Length
    invariant forall j :: j in readyQueue ==> 0 <= j < n
    invariant forall j :: j in readyQueue ==> processes[j].inQueue == true && processes[j].isComplete == false
    //invariant forall p :: (p in processes[..] && p.arrivalTime > currentTime) ==> (p.inQueue == false && p.isComplete == false) 
{
    if processes[i].arrivalTime <= currentTime
        && !processes[i].inQueue
        && !processes[i].isComplete
    {
    processes[i].inQueue := true;
    newQueue := newQueue + [i];
    }
    i := i + 1;
}
}

// Pops the head of readyQueue, runs it for up to 'quantum',
// updates times and re-queues or marks complete.
method UpdateQueue(
    processes: array<Process>, n: int,
    quantum: int,
    readyQueue: seq<int>,
    currentTime: int,
    programsExecuted: int)
returns (
    newQueue: seq<int>,
    updatedTime: int,
    updatedExecuted: int)
{
var i := readyQueue[0];
newQueue := readyQueue[1..];
var ct := currentTime;
var pe := programsExecuted;

if processes[i].burstTimeRemaining <= quantum {
    // finish it
    processes[i].isComplete := true;
    ct := ct + processes[i].burstTimeRemaining;
    processes[i].completionTime := ct;
    processes[i].waitingTime :=
    ct - processes[i].arrivalTime - processes[i].burstTime;
    if processes[i].waitingTime < 0 {
    processes[i].waitingTime := 0;
    }
    processes[i].turnaroundTime :=
    processes[i].waitingTime + processes[i].burstTime;
    processes[i].burstTimeRemaining := 0;
    pe := pe + 1;
    if pe < n {
    newQueue := CheckForNewArrivals(processes, n, ct, newQueue);
    }
} else {
    // pre-empt after one quantum
    processes[i].burstTimeRemaining := processes[i].burstTimeRemaining - quantum;
    ct := ct + quantum;
    if pe < n {
    newQueue := CheckForNewArrivals(processes, n, ct, newQueue);
    }
    newQueue := newQueue + [i];
}

updatedTime := ct;
updatedExecuted := pe;
}

// The core loop: seed the queue with process 0, then keep calling UpdateQueue
method RoundRobin(
    processes: array<Process>, n: int,
    quantum: int)
    requires processes.Length == n && quantum > 0 && n > 0
    modifies processes, processes[..]
{
var readyQueue := [0];
processes[0].inQueue := true;
var currentTime := 0;
var programsExecuted := 0;

while |readyQueue| > 0
    invariant 0 <= |readyQueue| <= n
    invariant forall i :: i in readyQueue ==> i < n
    // invariant forall i :: i in readyQueue ==> processes[i].inQueue == true && processes[i].isComplete == false
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
method Output(processes: array<Process>, n: int)
{
// Simple selection-sort by PID
var i := 0;
while i < n
    decreases n - i
{
    var j := i + 1;
    while j < n
    decreases n - j
    {
    if processes[j].pid < processes[i].pid {
        var tmp := processes[i];
        processes[i] := processes[j];
        processes[j] := tmp;
    }
    j := j + 1;
    }
    i := i + 1;
}

// Now print
i := 0;
var sumW := 0;
var sumT := 0;
while i < n
    decreases n - i
{
    print "Process ", processes[i].pid, 
        ": Waiting Time=", processes[i].waitingTime,
        " Turnaround Time=", processes[i].turnaroundTime, "\n";
    sumW := sumW + processes[i].waitingTime;
    sumT := sumT + processes[i].turnaroundTime;
    i := i + 1;
}
print "Average Waiting Time=", sumW as real / n as real, "\n";
print "Average Turnaround Time=", sumT as real / n as real, "\n";
}

// Example "main" – construct some processes, run, and output.
method Main()
{
var n := 4;
var quantum := 3;
var processes := new Process[n];
processes[0] := new Process(1, 0, 5);
processes[1] := new Process(2, 1, 3);
processes[2] := new Process(3, 2, 8);
processes[3] := new Process(4, 3, 6);

RoundRobin(processes, n, quantum);
Output(processes, n);
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
}
*/