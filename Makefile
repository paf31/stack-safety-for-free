all:
	pandoc -f markdown+yaml_metadata_block --filter pandoc-citeproc index.markdown -o index.pdf 
