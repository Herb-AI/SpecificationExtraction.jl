# SpecificationExtraction.jl

Requires a `python` installation with `sympy` installed. If this package
(SpecificationExtraction.jl) precompiles successfully, then `sympy` is
installed correctly. If you've installed `sympy`, and precompilation still
fails, then you may need to set the `PYTHON` environment variable to point to
the correct `python` executable, and rebuild the `PyCall` package 
(`Pkg.build("PyCall")`).

## Testing

Run `julia test/runtests.jl` to run the tests.