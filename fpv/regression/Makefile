
.PHONY: all gen clean

# Default target: generate all yamls
all: gen

# Generate all regression yamls using gen_all.py
gen:
	@echo "Generating regression yamls..."
	python3 gen_all.py

# Remove generated yamls
clean:
	@echo "Cleaning generated yamls..."
	rm -rf generated/*
