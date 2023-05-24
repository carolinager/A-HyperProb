FROM movesrwth/stormpy:1.7.0

# Obtain latest version of A-HyperProb from public repository
WORKDIR /opt/
RUN git clone -b existAsynchHyper https://github.com/carolinager/A-HyperProb

# Switch to HyperProb directory
WORKDIR /opt/A-HyperProb

# Install dependencies for HyperProb
RUN pip3 install .

# To create a separate container for a specific A-HyperProb command:
# uncomment the following line and insert the command
#CMD python3 hyperprob.py <insert_command_here>
