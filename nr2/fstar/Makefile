FSTAR_EXE ?= fstar.exe
FSTAR_FLAGS = --z3rlimit 60 --max_fuel 8 --max_ifuel 4

SRC_DIR = src
OUT_DIR = out
SRC_FILES = $(SRC_DIR)/QR.Matrix.fst \
            $(SRC_DIR)/QR.Decompose.fst \
            $(SRC_DIR)/QR.Proofs.fst \
            $(SRC_DIR)/QR.Tests.fst \
            $(SRC_DIR)/QR.Fuzz.fst

.PHONY: all verify clean

all: verify

verify: $(SRC_FILES)
	@echo "=== Verifying F* modules ==="
	@for f in $(SRC_FILES); do \
		echo "  Checking $$f ..."; \
		$(FSTAR_EXE) $(FSTAR_FLAGS) --include $(SRC_DIR) $$f || exit 1; \
		echo "  ✓ $$f"; \
	done
	@echo "=== All modules verified ==="

clean:
	rm -rf $(SRC_DIR)/.cache $(OUT_DIR)/*.ml
