
# for file in ground_formatted/*.dfy; do
#   #~/dafny/Binaries/Dafny format "$file"
#   name=$(basename "$file")
#   sed -E "/\/\*/{ :loop; /\*\//!{ N; b loop }; s/\/\*.*?\*\///g }" "$file" | sed -E 's:\/\/.*::' > "ground_wo_comments/${name}"
# done

#for file in ground_wo_comments/*.dfy; do
#  echo $file
#  timeout 60s ~/dafny/Binaries/Dafny verify --allow-warnings "$file"
#  exit_code=$?
  
#  if [ $exit_code -ne 0 ]; then
#    echo $exit_code
#    echo "$file\n" >> failures.txt
#  fi
##  sed -E "/\/\*/{ :loop; /\*\//!{ N; b loop }; s/\/\*.*?\*\///g }" "$file" | sed -E 's:\/\/.*::' > "${file}.cleaned"
#done
# mkdir ground_filtered

# mkdir ground_modules
# # rsync -av --exclude='*class*' --exclude='*trait*' --exclude='*iterator*' --exclude='*field*' --exclude='*constructor*' --exclude='*least predicate*' ground_truth/ ground_modules/
# # find ground_truth -type f ! -name "greatest predicate" ! -name "class" ! -name "trait" ! -name "module" ! -name "iterator" ! -name "field" ! -name "constructor" ! -name "function method" ! -name "predicate method" ! -name "least predicate" -exec cp {} ground_filtered/ \;
# grep -l "module" ground_truth/* -R | xargs grep -L -E "class|trait|iterator|constructor" | while read file; do
#     cp "$file" ground_modules/
# done

mkdir ground_combined
# rsync -av --exclude='*class*' --exclude='*trait*' --exclude='*iterator*' --exclude='*field*' --exclude='*constructor*' --exclude='*least predicate*' ground_truth/ ground_modules/
# find ground_truth -type f ! -name "greatest predicate" ! -name "class" ! -name "trait" ! -name "module" ! -name "iterator" ! -name "field" ! -name "constructor" ! -name "function method" ! -name "predicate method" ! -name "least predicate" -exec cp {} ground_filtered/ \;
grep -l "class" ground_truth/* -R | xargs grep -l "module" | xargs grep -L -E "trait|iterator" | while read file; do
    cp "$file" ground_combined/
done

# mkdir ground_annotated_new
# for file in ground_filtered/*.dfy; do
#   cp "$file" ground_annotated_new/
#   name=ground_annotated_new/$(basename "$file")
#   ~/Nagini-Convertion/Binaries/Dafny format "$name"
# done


# for file in ground_annotated_new/*.dfy; do
#  echo $file
#  timeout 60s ~/dafny/Binaries/Dafny verify --allow-warnings "$file"
#  exit_code=$?
  
#  if [ $exit_code -ne 0 ]; then
#    echo $exit_code
#    echo "$file\n" >> failures_ann.txt
#  fi
# #  sed -E "/\/\*/{ :loop; /\*\//!{ N; b loop }; s/\/\*.*?\*\///g }" "$file" | sed -E 's:\/\/.*::' > "${file}.cleaned"
# done


# for file in postponed/*.dfy; do
#  echo $file
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings "$file"
# #  sed -E "/\/\*/{ :loop; /\*\//!{ N; b loop }; s/\/\*.*?\*\///g }" "$file" | sed -E 's:\/\/.*::' > "${file}.cleaned"
# done