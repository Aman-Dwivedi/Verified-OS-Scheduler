# Verified-OS-Scheduler
 This project successfully implemented a single-core Round-Robin process scheduler and applied formal verification techniques using Dafny to establish its correctness. The work underscores the critical importance of formal correctness in the design and implementation of operating system process schedulers, particularly in light of the increasing complexity driven by modern hardware architectures.

 In order to run the Python compiled version of the verified process scheduler, run the __main__.py file. This will run the process scheduler class within module_.py. It will prompt to run a unit test or enter a custom set of processes to run with some enforcements on the process types. Make sure to have all the Python files in the same folder while running the program.

 In order to verify the correctness of the scheduler, please take a look at RoundRobinScheduler.dfy. It consists of all the lemmas used to prove the correctness of the scheduling algorithm along with two axioms (arguing their truth values) crucial for the formal verification of the Round-Robin algorithm.
