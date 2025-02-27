# rm -rf ground_modules_valid
# mkdir ground_modules_valid
# for file in ground_modules/*.dfy; do
#  echo $file
#  name=$(basename "$file")
# #  echo "module Gen {" >> ground_modules_valid/"$name"
# #  cat "$file" >> ground_modules_valid/"$name"
# #  echo "}" >> ground_modules_valid/"$name"
#  cat "$file" > ground_modules_valid/"$name"
#  ~/Nagini-Convertion/Binaries/Dafny validate ground_modules_valid/"$name"
# #  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings ground_modules_valid/"$name"
# done

# rm -rf ground_classes_valid
# mkdir ground_classes_valid
# for file in ground_classes/*.dfy; do
#  echo $file
#  name=$(basename "$file")
# #  echo "module Gen {" >> ground_classes_valid/"$name"
# #  cat "$file" >> ground_classes_valid/"$name"
# #  echo "}" >> ground_classes_valid/"$name"
#  cat "$file" > ground_classes_valid/"$name"
#  ~/Nagini-Convertion/Binaries/Dafny validate ground_classes_valid/"$name"
# #  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings ground_classes_valid/"$name"
# done


# for file in ground_classes_valid/*.dfy; do
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings $file
# done

# rm -rf ground_combined_valid
# mkdir ground_combined_valid
# for file in ground_combined/*.dfy; do
#  echo $file
#  name=$(basename "$file")
# #  echo "module Gen {" >> ground_modules_valid/"$name"
# #  cat "$file" >> ground_modules_valid/"$name"
# #  echo "}" >> ground_modules_valid/"$name"
#  cat "$file" > ground_combined_valid/"$name"
#  ~/Nagini-Convertion/Binaries/Dafny validate ground_combined_valid/"$name"
# #  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings ground_modules_valid/"$name"
# done


rm -rf ground_annotated_new_valid
mkdir ground_annotated_new_valid
for file in ground_annotated_new/*.dfy; do
 echo $file
 name=$(basename "$file")
#  echo "module Gen {" >> ground_modules_valid/"$name"
#  cat "$file" >> ground_modules_valid/"$name"
#  echo "}" >> ground_modules_valid/"$name"
 cat "$file" > ground_annotated_new_valid/"$name"
 ~/Nagini-Convertion/Binaries/Dafny validate ground_annotated_new_valid/"$name"
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings ground_modules_valid/"$name"
done

