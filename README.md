

## Files

- SAT Instances: `uf20-01.cnf`, `uf20-02.cnf` and `uf50-01.cnf`
- GWSAT: `GWSAT.py`
- WalkSAT + Tabu: `WalkSAT.py`
- SAT Checker: `SATChecker.py`

## Instructions

Open the terminal and run the algorithms in the folder provided as current directory:

```
GWSAT: python3 GWSAT.py [instance] [executions] [max_flips] [max_tries] [wp]
WalkSAT + Tabu: python3 WalkSAT.py [instance] [executions] [max_flips] [max_tries] [p] [tl]
```

**Examples:**

```
python3 GWSAT.py ../data/uf20-01.cnf 100 1000 10 0.4
python3 WalkSAT.py ../data/uf20-01.cnf 100 1000 10 0.4 5
```

Update the parameters as you wish:

- `instance`: A CNF formulae encoded in DIMACS CNF format.
- `executions`: int. It has to be greater than 0.
- `max_flips`: int. It has to be greater than 0.
- `max_tries`: int. It has to be greater than or equal to 0.
- `wp`: float or int. It can get values from 0 to 1, both included.
- `p`: float or int. It can get values from 0 to 1, both included.
- `tl`: int. It can get any value greater than or equal to 0.

Check the output file generated in the current working directory. 

**Example:** 

If you run instance `uf20_02.cnf` using any of the two algorithms, the following 
`.txt` file will be generated at the end of the executions:

`solution_uf20_02.cnf.txt`