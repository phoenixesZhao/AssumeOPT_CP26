## Compilation

In the root directory:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make

## Experiments

All competitors are executed with default parameters. For AssumeOPT:

- to run the proposed AssumeOPT (Used in Table 1 and Table 2)
    
        ./agls --time=xxx 

- to run NoInit in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-init-heuristic=default

- to run ExpR in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-arms=greedy

- to run ExpT in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-arms=exploit

- to run ExpR+ExpT in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-arms=greedy_exploit

- to run ExpR+Empty in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-arms=greedy_linear

- to run ExpT+Empty in ablation study (in Table 5)
  
        ./agls --time=xxx --agls-arms=exploit_linear

- to runEmpty in ablation study (in Table 5)
  
        ./agls --opt-mode=linear --time=xxx
