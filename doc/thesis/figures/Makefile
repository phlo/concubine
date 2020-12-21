EXPERIMENTS = ../../../experiments

DELIMITER = |

GENERATOR = | sed 's/ /$(DELIMITER)/g' > $@.dat

ENCODER_ARGS = -t encoder --encoder-time 1000
ENCODER_STATS = ./experiment-stats.sh $(ENCODER_ARGS) $^ $(GENERATOR)

SOLVER_ARGS = -t solver
SOLVER_STATS = ./experiment-stats.sh $(SOLVER_ARGS) $^ $(GENERATOR)

#------------------------------------------------------------------------------#

.PHONY: experiments
experiments: litmus count

#------------------------------------------------------------------------------#

LITMUS_INTEL = $(EXPERIMENTS)/litmus/intel

.PHONY: litmus-intel-encoder
litmus-intel-encoder: $(LITMUS_INTEL)
	$(ENCODER_STATS)

.PHONY: litmus-intel-solver
litmus-intel-solver: $(LITMUS_INTEL)
	$(SOLVER_STATS)

.PHONY: litmus-intel
litmus-intel: litmus-intel-encoder litmus-intel-solver

LITMUS_AMD = $(EXPERIMENTS)/litmus/amd

.PHONY: litmus-amd-encoder
litmus-amd-encoder: $(LITMUS_AMD)
	$(ENCODER_STATS)

.PHONY: litmus-amd-solver
litmus-amd-solver: $(LITMUS_AMD)
	$(SOLVER_STATS)

.PHONY: litmus-amd
litmus-amd: litmus-amd-encoder litmus-amd-solver

.PHONY: litmus
litmus: litmus-intel litmus-amd

#------------------------------------------------------------------------------#

COUNT_BUGGY = $(EXPERIMENTS)/count/buggy.*

.PHONY: count-buggy-encoder
count-buggy-encoder: $(COUNT_BUGGY)
	$(ENCODER_STATS)

.PHONY: count-buggy-solver
count-buggy-solver: $(COUNT_BUGGY)
	$(SOLVER_STATS)

.PHONY: count-buggy
count-buggy: count-buggy-encoder count-buggy-solver

COUNT_CAS = $(EXPERIMENTS)/count/cas.*

.PHONY: count-cas-encoder
count-cas-encoder: $(COUNT_CAS)
	$(ENCODER_STATS)

.PHONY: count-cas-solver
count-cas-solver: $(COUNT_CAS)
	$(SOLVER_STATS)

.PHONY: count-cas
count-cas: count-cas-encoder count-cas-solver

.PHONY: count
count: count-buggy count-cas
