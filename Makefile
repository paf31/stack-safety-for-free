all:
	pandoc -f markdown+yaml_metadata_block+citations+header_attributes --filter pandoc-citeproc index.markdown -o index.pdf 
