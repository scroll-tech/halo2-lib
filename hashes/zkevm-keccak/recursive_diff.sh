#!/bin/bash

# Usage: ./recursive_diff.sh dir1 dir2 diff_output_dir

dir1="$1"
dir2="$2"
diff_output_dir="$3"

if [ -z "$dir1" ] || [ -z "$dir2" ] || [ -z "$diff_output_dir" ]; then
  echo "Usage: $0 dir1 dir2 diff_output_dir"
  exit 1
fi

mkdir -p "$diff_output_dir"

compare_files() {
  src="$1"
  dest="$2"
  diff_dir="$3"

  if [ -f "$src" ] && [ -f "$dest" ]; then
    git diff --no-index "$src" "$dest" > "$diff_dir"
  elif [ -f "$src" ]; then
    git diff --no-index "$src" /dev/null > "$diff_dir"
  elif [ -f "$dest" ]; then
    git diff --no-index /dev/null "$dest" > "$diff_dir"
  fi
}

find "$dir1" -type f | sort -u | while read -r file; do
  rel_path="${file#$dir1/}"
  rel_path="${rel_path#$dir2/}"
  file1="$dir1/$rel_path"
  file2="$dir2/$rel_path"
  diff_file="$diff_output_dir/$rel_path.diff"

  mkdir -p "$(dirname "$diff_file")"
  compare_files "$file1" "$file2" "$diff_file"
done

echo "Diffs saved to $diff_output_dir"
