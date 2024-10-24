#!/bin/bash

count_loc() {
	sed '/^\s*$/d' "$1" | wc -l
}

process_directory() {
	local total_loc=0
	local file_count=0

	while IFS= read -r -d '' file; do
		loc=$(count_loc "$file")
		total_loc=$((total_loc + loc))
		file_count=$((file_count + 1))
		echo "$file: $loc LOC"
	done < <(find "$1" -type f -name "*.v" -print0)

	echo -e "\nProcessed $file_count files"
	echo "Total LOC: $total_loc"
}

if [ $# -ne 1 ]; then
	echo "Usage: $0 <directory_path>"
	exit 1
fi

if [ ! -d "$1" ]; then
	echo "Error: $1 is not a valid directory"
	exit 1
fi

process_directory "$1"
