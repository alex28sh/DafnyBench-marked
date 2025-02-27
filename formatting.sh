
# mkdir ground_classes_annotated
# for file in ground_classes/*.dfy; do
#   cp "$file" ground_classes_annotated/
#   name=ground_classes_annotated/$(basename "$file")
#   ~/Nagini-Convertion/Binaries/Dafny format "$name"
# done


# mkdir ground_modules_annotated
# for file in ground_modules/*.dfy; do
#   cp "$file" ground_modules_annotated/
#   name=ground_modules_annotated/$(basename "$file")
#   ~/Nagini-Convertion/Binaries/Dafny format "$name"
# done


mkdir ground_combined_annotated
for file in ground_combined/*.dfy; do
  cp "$file" ground_combined_annotated/
  name=ground_combined_annotated/$(basename "$file")
  ~/Nagini-Convertion/Binaries/Dafny format "$name"
done