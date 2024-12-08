#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Nov 20 17:44:57 2024

@author: dgrimes and Tristan Hurley (22/12/2024).
"""
import numpy as np
from time import perf_counter
import random
import sys
from os import listdir
import os
from matplotlib import pyplot as plt
import pandas as pd

# Fixed seed (student id R00192994)
myStudentNum = 192994
random.seed(myStudentNum)


'''
Data structures
state:          the current candidate solution
clauses:        list of lists, each list contains the literal of the clause
unsat_clauses:  the index of each currently unsat clause
makecounts:     the current makecount for each variable 
                (number of currently unsat clauses involving the variable) 
breakcounts:    the current breakcount for each variable 
                (number of currently sat clauses involving the variable, 
                 where the variable is the only satisfying literal of the clause
                 i.e the clause will go unsat if this variable is flipped) 
litToClauses:   dictionary containing 2*vars entries, one for each literal associated with each variable

NB: The variables and their associated literatls are numbered 1..n rather than 0..n-1, 
so to allow us to index in with variable number without having to -1 every time, 
a lot of the data structures are set up to be of size n+1, with the first element 
(index 0) ignored
'''

class GSAT_solver:
    
    def __init__(self, file, _h, _wp, _maxFlips, _maxRestarts, _tl):
        self.maxFlips = _maxFlips   # input: Number of flips before restarting
        self.maxRestarts = _maxRestarts     # input: Number of restarts before exiting
        self.flips = 0              # current number of flips performed
        self.restarts = 0           # current number of restarts performed
        self.nVars, self.nClauses, self.clauses, self.litToClauses = -1,-1,[],{}
        self.readInstance(file)
        self.state = [0 for _ in range(self.nVars+1)]
        self.makecounts = np.zeros(self.nVars+1,dtype=int) # unsat that would go sat
        self.breakcounts = np.zeros(self.nVars+1,dtype=int) # sat that would go unsat
        self.lastFlip = np.zeros(self.nVars+1,dtype=int) # unsat that would go sat
        self.bestSol = [0 for _ in range(self.nVars)]   # Current best solution found so far
        self.bestObj = self.nClauses+1          # Current best objective found so far (obj of bestSol)
        self.breakcounts[0] = self.nClauses+1 # sat that would go unsat
        self.wp = _wp   # input: walk probability
        self.h = _h     # input: heuristic to choose variable
        self.tl = _tl

    def readInstance(self, fName):
        file        = open(fName, 'r')
        current_clause = []
        clauseInd = 0
    
        for line in file:
            data = line.split()
    
            if len(data) == 0:
                continue
            if data[0] == 'c':
                continue
            if data[0] == 'p':
                self.nVars  = int(data[2])
                self.nClauses    = int(data[3])
                
                continue
            if data[0] == '%':
                break
            if self.nVars == -1 or self.nClauses == -1:
                print ("Error, unexpected data")
                sys.exit(0)
    
            ##now data represents a clause
            for var_i in data:
                literal = int(var_i)
                if literal == 0:
                    self.clauses.append(current_clause)
                    current_clause = []
                    clauseInd += 1
                    continue
                current_clause.append(literal)
                if literal in self.litToClauses:
                    self.litToClauses[literal].add(clauseInd)
                else:
                    self.litToClauses[literal] = set([clauseInd])
                    
        for i in range(1,self.nVars+1):
            if i not in self.litToClauses:
                self.litToClauses[i] = set()
            if -i not in self.litToClauses:
                self.litToClauses[-i] = set()
                    
        if self.nClauses != len(self.clauses):
            print(self.nClauses, len(self.clauses))
            print ("Unexpected number of clauses in the problem")
            sys.exit(0)
        file.close()

    def generateSolution(self):
        for i in range(1, self.nVars+1):
            choice = [-1,1]
            self.state[i] = (i * random.choice(choice))

    def initial_cost(self):
        # Compute objective value of initial solution, reset counters and recompute
        self.obj = self.nClauses
        self.unsat_clauses = set()
        self.makecounts = np.zeros(self.nVars+1,dtype=int) # unsat that would go sat
        self.breakcounts = np.zeros(self.nVars+1,dtype=int) # sat that would go unsat
        self.breakcounts[0] = self.nClauses+1
        num_unsat = 0
        clsInd = 0
        for clause in self.clauses:
            satLits = 0
            breakV = 0
            cStatus = False
            for lit in clause:
                if lit in self.state:
                    cStatus = True
                    satLits += 1
                    breakV = lit
                if satLits > 1:
                    break
            if satLits == 1:
                self.breakcounts[abs(breakV)] += 1
            if not cStatus:
                num_unsat += 1
                self.unsat_clauses.add(clsInd)
                for lit in clause:
                    self.makecounts[abs(lit)] += 1
            clsInd += 1
        self.obj = num_unsat
        if self.bestObj == -1:
            self.bestObj = num_unsat
            self.bestSol = self.state[1:]

    def flip(self, variable):
        self.flips += 1
        self.state[variable] *= -1
        self.update_counts(variable)
        self.lastFlip[variable] = self.flips

    # Function to update objective value and counts of variables 
    # Run after flipping 
    def update_counts(self, variable):
        literal = self.state[variable]
        for clauseInd in self.litToClauses[literal]:
            satLits = 0
            if clauseInd in self.unsat_clauses:
                for lit in self.clauses[clauseInd]:
                    self.makecounts[abs(lit)] -= 1
                # Was unsat so only flipvar now satisfies it 
                self.breakcounts[variable] += 1
            else:
                for lit in self.clauses[clauseInd]:
                    if lit in self.state:
                        satLits += 1
                        if lit != literal:
                            breaklit = lit
                if satLits == 2:
                    self.breakcounts[abs(breaklit)] -=1
        self.unsat_clauses = self.unsat_clauses - self.litToClauses[literal]
        self.obj = len(self.unsat_clauses)
        for clauseInd in self.litToClauses[literal*(-1)]:
            satLits = 0
            cStatus = False
            for lit in self.clauses[clauseInd]:
                if lit in self.state:
                    cStatus = True
                    satLits += 1
                    breaklit = lit
            if satLits == 1:
                self.breakcounts[abs(breaklit)] += 1
            if not cStatus:
                self.breakcounts[variable] -= 1 # flipvar was only 1 satisfying it
                self.obj += 1
                self.unsat_clauses.add(clauseInd)
                for lit in self.clauses[clauseInd]:
                    self.makecounts[abs(lit)] += 1

    def selectVar(self):
        if self.h =="gsat":
            return self.selectGSATvar()
        elif self.h == "gwsat":
            return self.selectGWSATvar()
        elif self.h == "gsatTabu":
            return self.selectGSATtabuvar()
        elif self.h == "hsat":
            return self.selectHSATvar()
        elif self.h == "hwsat":
            return self.selectHWSATvar()
        elif self.h == "walksat":
            return self.selectWalkSATvar()
        elif self.h == "walksatTabu":
            return self.selectWalkSATtabuvar()
        else:
            return self.selectGrimesSATvar()

        
    def selectGWSATvar(self):
        if random.random() < self.wp:
            nextvar = self.selectRWvar()
        else:
            nextvar = self.selectGSATvar()
        return nextvar

    def selectHSATvar(self):
        gains = self.makecounts-self.breakcounts
        hvars = np.where( gains == np.amax(gains))[0]
        return hvars[np.where(self.lastFlip[hvars]== np.amin(self.lastFlip[hvars]))[0]][0]

    def selectHWSATvar(self):
        if random.random() < self.wp:
            nextvar = self.selectRWvar()
        else:
            nextvar = self.selectHSATvar()
        return nextvar
    
    def selectGSATvar(self):
        gains = self.makecounts-self.breakcounts
        hvars = np.where( gains == np.amax(gains))[0]
        return np.random.choice(hvars)
        
    def selectRWvar(self):
        hvars = np.where( self.makecounts > 0 )[0]
        return np.random.choice(hvars)

    def selectWalkSATvar(self):
        nextCls = random.choice(tuple(self.unsat_clauses))
        varsCls = [abs(lit) for lit in self.clauses[nextCls]]
        gains = np.array([self.breakcounts[i] for i in varsCls])
        hvars = np.where( gains == 0)[0]
        if len(hvars)>0:
            return varsCls[np.random.choice(hvars)]
        elif random.random() < self.wp:
            return random.choice(varsCls)
        else:
            hvars = np.where( gains == np.amin(gains))[0]
            return varsCls[np.random.choice(hvars)]

    #Deliverable algorithm 1.
    def selectGSATtabuvar(self):
        """
        GSAT with Tabu Search:
        - Uses tabu list to prevent cycling
        - Aspiration allows tabu moves if they improve best solution this attempt
        - Otherwise selects best non-tabu variable
        """
        gains = self.makecounts - self.breakcounts
        current_cost = self.obj  # Current number of unsatisfied clauses

        # Find all possible improvements
        possible_moves = []
        for var in range(1, self.nVars + 1):
            new_cost = current_cost - gains[var]
            is_tabu = (self.flips - self.lastFlip[var]) <= self.tl
            
            # Apply aspiration: Allow tabu move if it improves best this attempt
            if new_cost < self.bestObj:
                return var
                
            # Add non-tabu moves to possible moves
            if not is_tabu:
                possible_moves.append(var)
        
        # If no non-tabu moves, allow all moves
        if not possible_moves:
            possible_moves = range(1, self.nVars + 1)
        
        # Among allowed moves, select one with best gain
        best_gain = max(gains[var] for var in possible_moves)
        best_vars = [var for var in possible_moves if gains[var] == best_gain]
        
        # Break ties by choosing least recently flipped
        return min(best_vars, key=lambda var: self.lastFlip[var])


    #Deliverable algorithm 2. 
    def selectGrimesSATvar(self):
        """
        Implements GrimesSAT heuristic:
        (a) If promising variable, select variable with largest net gain > 0.
        (b) Otherwise, randomly choose an unsatisfied clause:
            i. Random walk step with probability wp: choose a variable of clause at random.
            ii. Otherwise, choose variable with maximum net gain, breaking ties by choosing the least recently flipped.
        """
        # Step (a): Check for promising variables (net gain > 0)
        gains = self.makecounts - self.breakcounts  # Calculate net gains for all variables
        promising_vars = np.where(gains > 0)[0]  # Find promising variables with net gain > 0

        if len(promising_vars) > 0:
            # Select the variable with the largest net gain > 0
            return promising_vars[np.argmax(gains[promising_vars])]

        # Step (b): No promising variable found, pick a random unsatisfied clause
        next_clause = random.choice(tuple(self.unsat_clauses))
        clause_vars = [abs(lit) for lit in self.clauses[next_clause]]

        # (i) Random walk step with probability wp
        if random.random() < self.wp:
            return random.choice(clause_vars)

        # (ii) Otherwise, choose variable with maximum net gain, breaking ties by least recently flipped
        clause_gains = np.array([gains[var] for var in clause_vars])  # Gains of variables in the clause
        max_gain_vars = np.where(clause_gains == np.max(clause_gains))[0]  # Variables with max gain

        # Break ties by choosing the least recently flipped variable
        tied_vars = [clause_vars[i] for i in max_gain_vars]
        return min(tied_vars, key=lambda var: self.lastFlip[var])


        
    def solve(self):
        self.restarts = 0
        while self.restarts < self.maxRestarts and self.bestObj > 0:
            self.restarts += 1
            self.generateSolution()
            self.initial_cost()
            self.flips = 0
            self.lastFlip = np.zeros(self.nVars+1,dtype=int)
            while self.flips < self.maxFlips and self.bestObj > 0:
                nextvar = self.selectVar()
                self.flip(nextvar)
                if self.obj < self.bestObj:
                    self.bestObj = self.obj
                    self.bestSol = self.state[1:]

        if self.bestObj == 0:
            solutionChecker(self.clauses, self.bestSol)
        return self.flips, self.restarts, self.bestObj

def solutionChecker(clauses, sol):
    unsat_clause = 0
    for clause in clauses:
        cStatus = False
        for var in clause:
            if var in sol:
                cStatus = True
                break
        if not cStatus:
            unsat_clause+=1
    if unsat_clause > 0:
        print ("UNSAT Clauses: ",unsat_clause)
        return False
    return True

#Function to calculate descriptive statistics where possible to save on redundant code. 
def calculate_descriptive_stats(results):
   """Calculate descriptive statistics across all instances"""
   metrics = {
       "Solved": 1,
       "Objective": 2,
       "Restarts": 3,
       "Flips": 4,
       "Time": 5
   }
   
   stats = {}
   for name, idx in metrics.items():
       values = [r[idx] for r in results]
       stats[name] = {
           "mean": np.mean(values),
           "std": np.std(values),
           "min": np.min(values),
           "max": np.max(values),
           "median": np.median(values),
           "25th": np.percentile(values, 25),
           "75th": np.percentile(values, 75)
       }
   return stats

#Function to plot descriptive statstics. Saves plots to local directory. 
def plot_algorithm_boxplots(results, title, save_path):
    """Plot all metrics in one figure with 4 subplots"""
    metrics = ["Obj", "Res", "Flips", "Time"]
    fig, axes = plt.subplots(1, 4, figsize=(24, 8))
    fig.suptitle(title, fontsize=20, fontweight='bold')
    
    labels = list(results.keys())
    for i, metric in enumerate(metrics):
        data = [[r[i+2] for r in res] for res in results.values()]
        bp = axes[i].boxplot(data, labels=labels, patch_artist=True, boxprops=dict(facecolor='blue', color='blue'))
        axes[i].set_title(metric, fontsize=16, fontweight='bold')
        axes[i].tick_params(axis='both', labelsize=12)
        for label in axes[i].get_xticklabels() + axes[i].get_yticklabels():
            label.set_fontweight('bold')
        axes[i].set_ylabel(metric, fontsize=14, fontweight='bold')
        axes[i].set_xlabel("Parameter Values", fontsize=14, fontweight='bold')
        plt.setp(axes[i].get_xticklabels(), rotation=45)
    
    plt.tight_layout()
    #plt.savefig(save_path, dpi=300, bbox_inches='tight') uncomment to save plots locally. 
    plt.close()

def main():
   if len(sys.argv) == 1: 
       run_all_experiments()
   elif len(sys.argv) < 9:
       print ("Error - Incorrect input")
       print ("Expecting python gsat.py [fileDir] [alg] [number of runs] [max restarts]",
              "[max flips] [walk prob] [tabu length] [studentNum]")
       sys.exit(0)
   else:
       _, filesDir, alg, nRuns, maxRes, maxFlips, wp, tl, sNum  = sys.argv
       run_single_algorithm(filesDir, alg, int(nRuns), int(maxRes), int(maxFlips), 
                          float(wp), int(tl), int(sNum))

def run_single_algorithm(filesDir, alg, nRuns, maxRes, maxFlips, wp, tl, sNum): #kept for initial experimentatin and debugging of run_all_experiments().
   """Original main function logic for running a single algorithm"""
   statsList = ["Inst", "Solved:", "Obj:","Res:", "Flips:","Time:"]
   format_row = "{:>12}"*(len(statsList)) 
   print(alg, nRuns, maxRes, maxFlips, wp, tl)
   print(format_row.format(*statsList))
   results = []
   
   for filename in listdir(filesDir):
       if filename.endswith(str(sNum)[-1]+".cnf"):
           satInst=filesDir+"/"+filename
           avgRestarts, avgFlips, avgUnsatC, avgTime, unsolved = 0, 0, 0, 0, 0

           for i in range(nRuns):
               random.seed(sNum + i*100)
               np.random.seed(sNum + i*100)
               gsat = GSAT_solver(satInst, alg, wp, maxFlips, maxRes, tl)
               startPython = perf_counter()
               ctrFlips, ctrRestarts, ctrObj = gsat.solve()
               stopPython = perf_counter()
               avgFlips += ctrFlips
               avgRestarts += ctrRestarts
               avgUnsatC += ctrObj
               avgTime += (stopPython-startPython)
               if ctrObj > 0:
                   unsolved += 1
           
           result = [filename, nRuns - unsolved, avgUnsatC/nRuns, 
                    avgRestarts/nRuns, avgFlips/nRuns, round(avgTime/nRuns,3)]
           print(format_row.format(*result))
           results.append(result)
   
   return results

# Function to automate entire experiment rather than exhaustively manually changing paramters each time. Essential for plots.
def run_all_experiments():
   """Run all required experimental comparisons."""
   sNum = 192994 
   filesDir = "uf150-645"
   results_dir = "results"
   os.makedirs(results_dir, exist_ok=True)
   
   # 1. Compare all algorithms
   algorithms = ['gsat', 'gwsat', 'hwsat', 'gsatTabu', 'grimessat']
   comparison_results = {}
   for alg in algorithms:
       print(f"\nRunning {alg}...")
       results = run_single_algorithm(filesDir, alg, 10, 50, 1000, 0.2, 5, sNum)
       comparison_results[alg] = results
       print(f"\nDescriptive Statistics for {alg}:")
       stats = calculate_descriptive_stats(results)
       for metric, values in stats.items():
           print(f"\n{metric}:")
           for stat, value in values.items():
               print(f"{stat}: {value:.3f}")
   
   plot_algorithm_boxplots(comparison_results, "Algorithm Comparison", 
                         'results/algorithm_comparison.png')
   
   # 2. Parameter study: nRestarts/nFlips for GWSAT
   restart_flip_pairs = [(10, 5000), (25, 2000), (50, 1000), (100, 500), (200, 250)]
   gwsat_param_results = {}
   for restarts, flips in restart_flip_pairs:
       print(f"\nGWSAT with {restarts} restarts, {flips} flips")
       results = run_single_algorithm(filesDir, 'gwsat', 10, restarts, flips, 0.2, 5, sNum)
       gwsat_param_results[f"{restarts}_{flips}"] = results
       print(f"\nDescriptive Statistics:")
       stats = calculate_descriptive_stats(results)
       for metric, values in stats.items():
           print(f"\n{metric}:")
           for stat, value in values.items():
               print(f"{stat}: {value:.3f}")
   
   plot_algorithm_boxplots(gwsat_param_results, "GWSAT Parameter Study",
                         'results/gwsat_params_box.png')
   
   # 3. WP parameter study for GrimesSAT
   wp_values = [0.1, 0.2, 0.3, 0.4, 0.5]
   grimes_param_results = {}
   for wp in wp_values:
       print(f"\nGrimesSAT with wp={wp}")
       results = run_single_algorithm(filesDir, 'grimessat', 10, 50, 1000, wp, 5, sNum)
       grimes_param_results[str(wp)] = results
       print(f"\nDescriptive Statistics:")
       stats = calculate_descriptive_stats(results)
       for metric, values in stats.items():
           print(f"\n{metric}:")
           for stat, value in values.items():
               print(f"{stat}: {value:.3f}")
               
   plot_algorithm_boxplots(grimes_param_results, "GrimesSAT WP Study",
                         'results/grimes_params_box.png')
       
   # 4. Tabu length study for GSATTabu
   tl_values = [2, 5, 10, 20, 50]
   tabu_param_results = {}
   for tl in tl_values:
       print(f"\nGSATTabu with tl={tl}")
       results = run_single_algorithm(filesDir, 'gsatTabu', 10, 50, 1000, 0.2, tl, sNum)
       tabu_param_results[str(tl)] = results
       print(f"\nDescriptive Statistics:")
       stats = calculate_descriptive_stats(results)
       for metric, values in stats.items():
           print(f"\n{metric}:")
           for stat, value in values.items():
               print(f"{stat}: {value:.3f}")
               
   plot_algorithm_boxplots(tabu_param_results, "GSATTabu TL Study",
                         'results/tabu_params_box.png')
   
   # 5. Runtime distribution for HSAT vs HWSAT
   print("\nRunning runtime distribution analysis...")
   run_runtime_distribution(sNum)

def run_runtime_distribution(sNum):
    """Run HSAT vs HWSAT comparison with 100 runs each"""
    fifty_var_dir = "uf50-218"
    results_dir = "results" #showing unused due to commenting out of plot saving synta at bottom of function.
    
    all_instances = [f for f in listdir(fifty_var_dir) if f.endswith('.cnf')]
    instances = random.sample(all_instances, 2)
    print("Selected 50-variable instances for RTD analysis:", instances)
    
    for inst in instances:
        hsat_results = []
        hwsat_results = []
        
        for i in range(100):
            random.seed(sNum + i*100)
            np.random.seed(sNum + i*100)
            
            # Run HSAT
            gsat = GSAT_solver(fifty_var_dir+"/"+inst, 'hsat', 0.2, 1000, 50, 5)
            flips, restarts, obj = gsat.solve()
            hsat_results.append([inst, 1, obj, restarts, flips, 0])  

            # Run HWSAT
            gsat = GSAT_solver(fifty_var_dir+"/"+inst, 'hwsat', 0.2, 1000, 50, 5)
            flips, restarts, obj = gsat.solve()
            hwsat_results.append([inst, 1, obj, restarts, flips, 0])
        
        print(f"\nDescriptive Statistics for HSAT on instance {inst}:")
        stats = calculate_descriptive_stats(hsat_results)
        for metric, values in stats.items():
            print(f"\n{metric}:")
            for stat, value in values.items():
                print(f"{stat}: {value:.3f}")
                
        print(f"\nDescriptive Statistics for HWSAT on instance {inst}:")
        stats = calculate_descriptive_stats(hwsat_results)
        for metric, values in stats.items():
            print(f"\n{metric}:")
            for stat, value in values.items():
                print(f"{stat}: {value:.3f}")
        
        # Plot RTD
        plt.figure(figsize=(12, 8))
        plt.hist([r[4] for r in hsat_results], alpha=0.5, label='HSAT', bins=20)
        plt.hist([r[4] for r in hwsat_results], alpha=0.5, label='HWSAT', bins=20)
        plt.xlabel('Number of Flips', fontsize=14, fontweight='bold')
        plt.ylabel('Frequency', fontsize=14, fontweight='bold')
        plt.title(f'Runtime Distribution - Instance {inst}', fontsize=16, fontweight='bold')
        plt.tick_params(axis='both', labelsize=12)
        for label in plt.gca().get_xticklabels() + plt.gca().get_yticklabels():
            label.set_fontweight('bold')
        plt.legend(fontsize=12, frameon=True)
        plt.tight_layout()
        #plt.savefig(f'{results_dir}/runtime_dist_{inst}.png', dpi=300, bbox_inches='tight') #uncomment this line to save plots locally
        plt.close()

main()