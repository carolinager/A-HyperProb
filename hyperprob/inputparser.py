import argparse


def parseArguments():
    parser = argparse.ArgumentParser(description='Model checks an Markov Chain against a given HyperPCTL specification.')
    parser.add_argument('-modelPath', required=True, help='path to the MDP/DTMC model file in PRISM language')
    parser.add_argument('-hyperString', required=True, help='the specification string in HyperPCTL')
    parser.add_argument('-stutterLength', required=False, help='Memory size for stutter scheduler')
    parser.add_argument('--checkModel', action='store_true', help='check if model file can be parsed')
    parser.add_argument('--checkProperty', action='store_true', help='check if property file can be parsed')
    parser.add_argument('--dontRestrictSched', action='store_true', help='Specify that no extra restrictions should be placed on the schedulers')
    args = parser.parse_args()
    return args
