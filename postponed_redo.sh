
# rm -rf postponed
# mkdir postponed
# for file in postponed/*.dfy; do
#  echo $file
#  name=$(basename "$file")
# #  cat ground_truth/"$name" > postponed/"$name"
# #  ~/Nagini-Convertion/Binaries/Dafny format postponed/"$name"
# done

# mkdir postponed_valid
# for file in postponed/*.dfy; do
#  echo $file
#  name=$(basename "$file")
#  cat postponed/"$name" > postponed_valid/"$name"
# #  ~/Nagini-Convertion/Binaries/Dafny format postponed/"$name"
#  ~/Nagini-Convertion/Binaries/Dafny validate postponed_valid/"$name"
# done

for file in postponed_valid/*.dfy; do
 echo $file
 name=$(basename "$file")
 timeout 60s ~/try_new/dafny/Binaries/Dafny verify --allow-warnings postponed_valid/"$name"
done

