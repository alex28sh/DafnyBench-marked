
# for file in ground_classes_valid/*.dfy; do
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings $file
# done


# for file in ground_modules_valid/*.dfy; do
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings $file
# done

# for file in ground_combined_valid/*.dfy; do
#  timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings $file
# done

for file in ground_annotated_new_valid/*.dfy; do
 timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings $file
done