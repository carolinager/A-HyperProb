# A-HyperProb

This package model checks asynchronous probabilistic hyperproperties written in A-HyperPCTL on MDPs.

## Installation

Begin by cloning this folder locally:
```
git clone https://github.com/carolinager/A-HyperProb
cd A-HyperProb
```
A-HyperProb depends on [stormpy](https://github.com/moves-rwth/stormpy) which has its own dependencies. Currently you can find scripts in the `resources` folder to help install the dependencies. The [README.md](resources/README.md) inside this folder provides a guide for these installations.


To install A-HyperProb run:
`pip install .` from the `HyperProb` folder.


## Run via docker (Recommended)

Get docker (https://www.docker.com/get-started/) and clone A-HyperProb locally:
```
git clone https://github.com/carolinager/A-HyperProb
cd A-HyperProb
```
or simply download the Dockerfile provided in the repository.

Build an image:
```
docker build -t ahyperprob .
```
Run the image as a container:
```
docker run -it ahyperprob
```

## Example applications with expected runtimes
####SSPOD:
Expected Runtime:

```
-modelPath ./benchmark/CE/th01.nm
-hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) .
  ( (h1(t1) & h2(t2)) -> (P(F terml1(t1)) = P(F terml1(t2))) )"
-stutterLength 2
```

####TL:
Expected Runtime:

```
-modelPath ./benchmark/TL/tl.nm
-hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) .
 ((i(t1) & i(t2)) -> (P(F j0(t1)) = P(F j0(t2))))"
-stutterLength 2
```

####ACDB:
Expected Runtime:

```
-modelPath ./benchmark/ACDB/acdb.nm
-hyperString "ES sh . A s1 . A s2 . ET t1 (s1). ET t2 (s2) .
  ((i(t1) & i(t2)) -> (P(G (P(X a(t1)) = P(X a(t2)))) = 1))"
-stutterLength 2
```


## Host platform on which docker was tested:
OS: Ubuntu 22.04.2
RAM: 32GB
Number of cores: 8
CPU frequency: 3.60GHz
