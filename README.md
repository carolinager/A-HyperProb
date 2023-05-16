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
TODO

Expected runtime: TODO

## Host platform on which docker was tested:
OS: Ubuntu 22.04.2
RAM: 32GB
Number of cores: 8
CPU frequency: 3.60GHz
