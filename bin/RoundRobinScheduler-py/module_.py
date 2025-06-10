import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def UniqueSeqLengthAtMostN(s, n):
        d_0_numbersSet_: _dafny.Set
        d_0_numbersSet_ = _dafny.Set({})
        d_1_i_: int
        d_1_i_ = 0
        while (d_1_i_) < (n):
            d_0_numbersSet_ = (d_0_numbersSet_) | (_dafny.Set({d_1_i_}))
            d_1_i_ = (d_1_i_) + (1)
        d_2_sSet_: _dafny.Set
        d_2_sSet_ = _dafny.Set({})
        d_3_j_: int
        d_3_j_ = 0
        while (d_3_j_) < (len(s)):
            d_2_sSet_ = (d_2_sSet_) | (_dafny.Set({(s)[d_3_j_]}))
            d_3_j_ = (d_3_j_) + (1)

    @staticmethod
    def SetOfIntegers(n):
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_0_i_: int = compr_0_
                if ((0) <= (d_0_i_)) and ((d_0_i_) < (n)):
                    coll0_ = coll0_.union(_dafny.Set([d_0_i_]))
            return _dafny.Set(coll0_)
        return iife0_()
        

    @staticmethod
    def ProcessQueueCurTime(processes, currentTime):
        def lambda0_(forall_var_0_):
            d_0_p_: Process = forall_var_0_
            return not ((d_0_p_) in (_dafny.SeqWithoutIsStrInference((processes)[::]))) or ((((d_0_p_.inQueue) == (True)) or ((d_0_p_.isComplete) == (True)) if (d_0_p_.arrivalTime) <= (currentTime) else ((d_0_p_.inQueue) == (False)) or ((d_0_p_.isComplete) == (False))))

        return _dafny.quantifier((_dafny.SeqWithoutIsStrInference((processes)[::])).UniqueElements, True, lambda0_)

    @staticmethod
    def AllPinProcessQueue(processes):
        def lambda0_(forall_var_0_):
            d_0_p_: Process = forall_var_0_
            return not ((d_0_p_) in (_dafny.SeqWithoutIsStrInference((processes)[::]))) or (not(((d_0_p_.inQueue) == (True)) and ((d_0_p_.isComplete) == (True))))

        return _dafny.quantifier((_dafny.SeqWithoutIsStrInference((processes)[::])).UniqueElements, True, lambda0_)

    @staticmethod
    def CheckForNewArrivals(processes, n, currentTime, readyQueue, extraInQueue):
        newQueue: _dafny.Seq = _dafny.Seq({})
        d_0_i_: int
        d_0_i_ = 0
        newQueue = readyQueue
        d_1_added_: bool
        d_1_added_ = False
        while (d_0_i_) < (n):
            if ((((processes)[d_0_i_].arrivalTime) <= (currentTime)) and (not((processes)[d_0_i_].inQueue))) and (not((processes)[d_0_i_].isComplete)):
                obj0_ = (processes)[d_0_i_]
                obj0_.inQueue = True
                newQueue = (newQueue) + (_dafny.SeqWithoutIsStrInference([d_0_i_]))
                d_1_added_ = True
            default__.UniqueSeqLengthAtMostN(newQueue, n)
            d_2_newSet_: _dafny.Set
            def iife0_():
                coll0_ = _dafny.Set()
                compr_0_: int
                for compr_0_ in _dafny.IntegerRange(0, n):
                    d_3_i_: int = compr_0_
                    if ((((0) <= (d_3_i_)) and ((d_3_i_) < (n))) and (((processes)[d_3_i_].isComplete) == (True))) and (((processes)[d_3_i_].inQueue) == (False)):
                        coll0_ = coll0_.union(_dafny.Set([d_3_i_]))
                return _dafny.Set(coll0_)
            d_2_newSet_ = iife0_()
            
            d_0_i_ = (d_0_i_) + (1)
        return newQueue

    @staticmethod
    def UpdateQueue(processes, n, quantum, readyQueue, currentTime, programsExecuted):
        newQueue: _dafny.Seq = _dafny.Seq({})
        updatedTime: int = int(0)
        updatedExecuted: int = int(0)
        updatedTime = currentTime
        updatedExecuted = programsExecuted
        d_0_i_: int
        d_0_i_ = (readyQueue)[0]
        newQueue = _dafny.SeqWithoutIsStrInference((readyQueue)[1::])
        if ((processes)[d_0_i_].burstTimeRemaining) <= (quantum):
            d_1_count_: _dafny.Set
            def iife0_():
                coll0_ = _dafny.Set()
                compr_0_: int
                for compr_0_ in _dafny.IntegerRange(0, n):
                    d_2_i_: int = compr_0_
                    if ((((0) <= (d_2_i_)) and ((d_2_i_) < (n))) and (((processes)[d_2_i_].isComplete) == (True))) and (((processes)[d_2_i_].inQueue) == (False)):
                        coll0_ = coll0_.union(_dafny.Set([d_2_i_]))
                return _dafny.Set(coll0_)
            d_1_count_ = iife0_()
            
            obj0_ = (processes)[d_0_i_]
            obj0_.inQueue = False
            obj1_ = (processes)[d_0_i_]
            obj1_.isComplete = True
            updatedTime = (currentTime) + ((processes)[d_0_i_].burstTimeRemaining)
            obj2_ = (processes)[d_0_i_]
            obj2_.completionTime = updatedTime
            obj3_ = (processes)[d_0_i_]
            obj3_.waitingTime = (((processes)[d_0_i_].completionTime) - ((processes)[d_0_i_].arrivalTime)) - ((processes)[d_0_i_].burstTime)
            if ((processes)[d_0_i_].waitingTime) < (0):
                obj4_ = (processes)[d_0_i_]
                obj4_.waitingTime = 0
            obj5_ = (processes)[d_0_i_]
            obj5_.turnaroundTime = ((processes)[d_0_i_].waitingTime) + ((processes)[d_0_i_].burstTime)
            obj6_ = (processes)[d_0_i_]
            obj6_.burstTimeRemaining = 0
            d_3_newcount_: _dafny.Set
            def iife1_():
                coll1_ = _dafny.Set()
                compr_1_: int
                for compr_1_ in _dafny.IntegerRange(0, n):
                    d_4_i_: int = compr_1_
                    if ((((0) <= (d_4_i_)) and ((d_4_i_) < (n))) and (((processes)[d_4_i_].isComplete) == (True))) and (((processes)[d_4_i_].inQueue) == (False)):
                        coll1_ = coll1_.union(_dafny.Set([d_4_i_]))
                return _dafny.Set(coll1_)
            d_3_newcount_ = iife1_()
            
            updatedExecuted = (programsExecuted) + (1)
            if (updatedExecuted) != (n):
                out0_: _dafny.Seq
                out0_ = default__.CheckForNewArrivals(processes, n, updatedTime, newQueue, False)
                newQueue = out0_
            elif True:
                pass
        elif True:
            d_5_count_: _dafny.Set
            def iife2_():
                coll2_ = _dafny.Set()
                compr_2_: int
                for compr_2_ in _dafny.IntegerRange(0, n):
                    d_6_i_: int = compr_2_
                    if ((((0) <= (d_6_i_)) and ((d_6_i_) < (n))) and (((processes)[d_6_i_].isComplete) == (True))) and (((processes)[d_6_i_].inQueue) == (False)):
                        coll2_ = coll2_.union(_dafny.Set([d_6_i_]))
                return _dafny.Set(coll2_)
            d_5_count_ = iife2_()
            
            obj7_ = (processes)[d_0_i_]
            obj7_.burstTimeRemaining = ((processes)[d_0_i_].burstTimeRemaining) - (quantum)
            updatedTime = (currentTime) + (quantum)
            newQueue = (newQueue) + (_dafny.SeqWithoutIsStrInference([d_0_i_]))
            out1_: _dafny.Seq
            out1_ = default__.CheckForNewArrivals(processes, n, updatedTime, newQueue, True)
            newQueue = out1_
        return newQueue, updatedTime, updatedExecuted

    @staticmethod
    def SeqProcSum(ps):
        if (len(ps)) == (0):
            return 0
        elif True:
            return ((default__.SeqProcSum(_dafny.SeqWithoutIsStrInference((ps)[:(len(ps)) - (1):]))) + ((ps)[(len(ps)) - (1)].arrivalTime)) + ((ps)[(len(ps)) - (1)].burstTime)

    @staticmethod
    def SumProcessTimes(ps):
        total: int = int(0)
        d_0_i_: int
        d_0_i_ = 0
        total = 0
        while (d_0_i_) < (len(ps)):
            total = ((total) + ((ps)[d_0_i_].arrivalTime)) + ((ps)[d_0_i_].burstTime)
            d_0_i_ = (d_0_i_) + (1)
        return total

    @staticmethod
    def RoundRobin(processes, n, quantum):
        programsExecuted: int = int(0)
        d_0_readyQueue_: _dafny.Seq
        d_0_readyQueue_ = _dafny.SeqWithoutIsStrInference([0])
        d_1_currentTime_: int
        d_1_currentTime_ = 0
        obj0_ = (processes)[0]
        obj0_.inQueue = True
        hi0_ = n
        for d_2_i_ in range(1, hi0_):
            if ((processes)[d_2_i_].arrivalTime) <= (d_1_currentTime_):
                obj1_ = (processes)[d_2_i_]
                obj1_.inQueue = True
                d_0_readyQueue_ = (d_0_readyQueue_) + (_dafny.SeqWithoutIsStrInference([d_2_i_]))
        default__.UniqueSeqLengthAtMostN(d_0_readyQueue_, n)
        programsExecuted = 0
        d_3_maxTime_: int
        out0_: int
        out0_ = default__.SumProcessTimes(processes)
        d_3_maxTime_ = out0_
        while ((programsExecuted) < (n)) and ((d_1_currentTime_) < (d_3_maxTime_)):
            d_4_newQueue_: _dafny.Seq = _dafny.Seq({})
            d_5_updatedTime_: int = int(0)
            d_6_updatedExecuted_: int = int(0)
            out1_: _dafny.Seq
            out2_: int
            out3_: int
            out1_, out2_, out3_ = default__.UpdateQueue(processes, n, quantum, d_0_readyQueue_, d_1_currentTime_, programsExecuted)
            d_4_newQueue_ = out1_
            d_5_updatedTime_ = out2_
            d_6_updatedExecuted_ = out3_
            d_0_readyQueue_ = d_4_newQueue_
            d_1_currentTime_ = d_5_updatedTime_
            programsExecuted = d_6_updatedExecuted_
        d_7_completedNotInQueue_: _dafny.Set
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, n):
                d_8_i_: int = compr_0_
                if ((((0) <= (d_8_i_)) and ((d_8_i_) < (n))) and (((processes)[d_8_i_].isComplete) == (True))) and (((processes)[d_8_i_].inQueue) == (False)):
                    coll0_ = coll0_.union(_dafny.Set([d_8_i_]))
            return _dafny.Set(coll0_)
        d_7_completedNotInQueue_ = iife0_()
        
        return programsExecuted

    @staticmethod
    def Main(noArgsParameter__):
        userInput = input("Enter number of processes: ")
        d_0_n_: int
        d_0_n_ = 4
        d_1_quantum_: int
        d_1_quantum_ = 1
        d_2_processes_: _dafny.Seq
        d_2_processes_ = _dafny.SeqWithoutIsStrInference([])
        d_3_temp_: Process
        nw0_ = Process()
        nw0_.ctor__(1, 0, 5)
        d_3_temp_ = nw0_
        d_2_processes_ = (d_2_processes_) + (_dafny.SeqWithoutIsStrInference([d_3_temp_]))
        nw1_ = Process()
        nw1_.ctor__(2, 1, 3)
        d_3_temp_ = nw1_
        d_2_processes_ = (d_2_processes_) + (_dafny.SeqWithoutIsStrInference([d_3_temp_]))
        nw2_ = Process()
        nw2_.ctor__(3, 2, 8)
        d_3_temp_ = nw2_
        d_2_processes_ = (d_2_processes_) + (_dafny.SeqWithoutIsStrInference([d_3_temp_]))
        nw3_ = Process()
        nw3_.ctor__(4, 3, 6)
        d_3_temp_ = nw3_
        d_2_processes_ = (d_2_processes_) + (_dafny.SeqWithoutIsStrInference([d_3_temp_]))
        d_4_completed_: int
        out0_: int
        out0_ = default__.RoundRobin(d_2_processes_, d_0_n_, d_1_quantum_)
        d_4_completed_ = out0_
        default__.printOutput(d_2_processes_)
    
    @staticmethod
    def printOutput(processes):
        for p in processes:
            print(f"Process ID: {p.pid}, Arrival: {p.arrivalTime}, Burst Time: {p.burstTime}, Burst Time Remaining: {p.burstTimeRemaining}, Completion Time: {p.completionTime}, Turn Around Time: {p.turnaroundTime}, Waiting Time: {p.waitingTime}, In Queue: {p.inQueue}, Completed? {p.isComplete}")


class Process:
    def  __init__(self):
        self.pid: int = int(0)
        self.arrivalTime: int = int(0)
        self.burstTime: int = int(0)
        self.burstTimeRemaining: int = int(0)
        self.completionTime: int = int(0)
        self.turnaroundTime: int = int(0)
        self.waitingTime: int = int(0)
        self.isComplete: bool = False
        self.inQueue: bool = False
        pass

    def __dafnystr__(self) -> str:
        return "_module.Process"
    def ctor__(self, id, arrival, burst):
        (self).pid = id
        (self).arrivalTime = arrival
        (self).burstTime = burst
        (self).burstTimeRemaining = burst
        (self).completionTime = 0
        (self).turnaroundTime = 0
        (self).waitingTime = 0
        (self).isComplete = False
        (self).inQueue = False

