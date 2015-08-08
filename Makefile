all:
	pandoc -f markdown+yaml_metadata_block+citations --filter pandoc-citeproc index.markdown -o index.pdf 
