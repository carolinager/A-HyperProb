FROM movesrwth/stormpy:1.7.0

# make ssh dir
RUN mkdir /root/.ssh/

# add ssh key
ADD id_rsa /root/.ssh/id_rsa
RUN chmod 600 /root/.ssh/id_rsa
RUN echo "StrictHostKeyChecking no " > /root/.ssh/config

# Obtain latest version of HyperProb from public repository
WORKDIR /opt/
RUN git clone -b asyncHyper git@github.com:oyendrila-dobe/HyperProbV2.git

# Switch to HyperProb directory
WORKDIR /opt/HyperProbV2

# Install dependencies for HyperProb
RUN pip3 install .

# Let it run
CMD python3 hyperprob.py -modelPath ./benchmark/test/mdp.nm -hyperString "ES sh . E s1 . ET t1 (s1). (hg0(t1) & (P(F le1(t1)) = 1))" -stutterLength 2
