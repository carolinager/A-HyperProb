# A-HyperProb

This package model checks asynchronous probabilistic hyperproperties written in A-HyperPCTL on MDPs.
The implementation is in python and uses the SMT solver Z3. It is based on the model-checking implementation for HyperPCTL: https://github.com/TART-MSU/HyperProb

## Run via Docker (Recommended)

### Getting Started
Get docker (https://www.docker.com/get-started/) and download the Dockerfile provided in the repository (https://github.com/carolinager/A-HyperProb) or clone A-HyperProb locally:

```
git clone https://github.com/carolinager/A-HyperProb
cd A-HyperProb
```

### Running - Option 1
Navigate to the folder containing the docker file.

Build an image, and then run the image as a container:

```
docker build -t ahyperprob .
docker run -it ahyperprob /bin/bash
```

You should then be able to run A-HyperProb commands from the current directory via ```python3 hyperprob.py <command>``` where ```<command>``` should be replaced by a A-HyperProb command (see examples below).

### Running - Option 2
To execute a specific A-HyperProb command in a single container, insert the following command at the end of the Dockerfile:
```CMD python3 hyperprob.py <command>```
where ```<command>``` should be replaced by a A-HyperProb command, and run:

```
docker build -t ahyperprob .
docker run -it ahyperprob
```

## Example Applications With Expected Runtimes
### Classic Example (CE):

Expected Runtime for ```th01```: 16sec <br>
Expected Runtime for ```th02```-```th05```: Solving did not finish in >1h

```-modelPath ./benchmark/CE/th01.nm -hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) . ( (h1(t1) & h2(t2)) -> (P(F terml1(t1)) = P(F terml1(t2))) )" -stutterLength 2```

Replace ```th01``` with ```th02```-```th05``` for different initial values of h.

### Timing Leak (TL):

Expected Runtime: Solving did not finish in >1h

```-modelPath ./benchmark/TL/tl.nm -hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) . ((i(t1) & i(t2)) -> (P(F j0(t1)) = P(F j0(t2))))" -stutterLength 2 ```

### ACDB:

Expected Runtime: Memory exceeded in 18 minutes

``` -modelPath ./benchmark/ACDB/acdb.nm -hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) .  ((i(t1) & i(t2)) -> (P(G (P(X a(t1)) = P(X a(t2)))) = 1))" -stutterLength 2```


## Explanation of A-HyperProb Commands

A-HyperProb commands are structured as follows:

```-modelPath <path_to_model> -hyperString <AHyperPCTL_formula> -stutterLength <stutter_memory_size>```

- hyperString syntax:
    - ES sh : existential scheduler quantification. Currently only a single scheduler variable is supported.
    - E s1 / A s1 : existential / universal state quantification. We assume that the state variables are named s1, ..., sn for some n, but they do not have to appear in this order
    - ET t1 (s1) : existential stutter quantification. We assume that the stutter-scheduler variables are named t1, ..., tn and that they appear in this order
    - non-quantified property: Consider the grammar in ```hyperprob/propertyparser.py``` for a detailed syntax. Special attention should be paid to correct placement of brackets.

- stutterLength: memory size for the stutter-schedulers. Value 1 corresponds to the trivial stutter-scheduler which does not stutter at all.


Optional parameters:

- checkProperty: set flag to check if the specified A-HyperPCTL formula is syntactically correct
- checkModel: set flag to check if the model file can be parsed
- maxSchedProb: specify an upper bound for the scheduler probabilities. This default value is 0.99


## Installation (Not Recommended)

Begin by cloning this folder locally:

```
git clone https://github.com/carolinager/A-HyperProb
cd A-HyperProb
```
A-HyperProb depends on [stormpy](https://github.com/moves-rwth/stormpy) which has its own dependencies. Currently you can find scripts in the `resources` folder to help install the dependencies. The [README.md](resources/README.md) inside this folder provides a guide for these installations.


To install A-HyperProb run:
`pip install .` from the `HyperProb` folder.


## People

### Authors:
  - [Lina Gerlach](https://ths.rwth-aachen.de/people/lina-gerlach/), RWTH Aachen.
  - [Oyendrila Dobe](https://oyendrila-dobe.github.io/), Michigan State University.  


### Other Contributors:
  - [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/), RWTH Aachen.
  - [Ezio Bartocci](https://informatics.tuwien.ac.at/people/ezio-bartocci), TU-Vienna.
  - [Borzoo Bonakdarpour](http://www.cse.msu.edu/~borzoo/), Michigan State University.   

## Acknowledgements

 - Oyendrila Dobe is supported by the United States National Science Foundation
 - Lina Gerlach is supported by DFG RTG 2236/2 UnRAVeL
