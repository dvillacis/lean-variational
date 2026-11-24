import VariationalAnalysis

-- Fails if a definition, structure, instance or theorem of the library has no docstring.
-- (`lake lint` does not run these two linters.)
#lint only docBlame docBlameThm in VariationalAnalysis
