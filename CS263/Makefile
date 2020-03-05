-include CONFIGURE

# INCLUDE_COMPCERT = -R $(COMPCERT_DIR) compcert
# INCLUDE_VST = $(foreach d, $(VST_DIRS), -Q $(VST_DIR)/$(d) VST.$(d))
# INCLUDE_RAMIFYCOQ = -R $(GRAPH_LIB_DIR) RamifyCoq
INCLUDE_CURRENT = -R $(CURRENT_DIR) PL

# NORMAL_FLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_CURRENT)
# CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_RAMIFYCOQ) $(INCLUDE_CURRENT)
# CODE_FLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_CURRENT) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
NORMAL_FLAG = $(INCLUDE_CURRENT)

PL_FILES = \
    Introduction.v Hoare_Logic_1.v Hoare_Logic_2.v 

LIB_FILES = \
	Imp.v

HW_FILES = \
	Assignment1.v


$(PL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(LIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(HW_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v


all: \
    $(LIB_FILES:%.v=%.vo) $(HW_FILES:%.v=%.vo) 

note: \
	$(LIB_FILES:%.v=%.vo) $(PL_FILES:%.v=%.vo) 

depend:
	$(COQDEP) $(NORMAL_FLAG) $(LIB_FILES) $(PL_FILES) $(HW_FILES) > .depend

.depend:
	@$(COQDEP) $(NORMAL_FLAG) $(LIB_FILES) $(PL_FILES) $(HW_FILES) > .depend

clean:
	@rm *.vo *.glob 

.DEFAULT_GOAL := all

include .depend

