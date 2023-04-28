FROM movesrwth/stormpy:1.7.0

# make ssh dir
RUN mkdir /root/.ssh/

# add ssh key
ADD id_rsa /root/.ssh/id_rsa
RUN chmod 600 /root/.ssh/id_rsa
RUN echo "StrictHostKeyChecking no " > /root/.ssh/config

# Obtain latest version of HyperProb from public repository
WORKDIR /opt/
RUN git clone -b asyncHyperCVC git@github.com:oyendrila-dobe/HyperProbV2.git

# Switch to HyperProb directory
WORKDIR /opt/HyperProbV2

# Install dependencies for HyperProb
RUN pip3 install .

# Let it run
CMD python3 hyperprob.py -modelPath ./benchmark/test/mdp.nm -hyperString "ES sh . E s1 . E s2 . AT t1 (s1). AT t2 (s2) . ((le1(t2) & hg0(t1)) & (P(X hg0(t1)) = 0.5 ))" -stutterLength 2
