import random
file = open("root/module.mf", "w")
for i in range(1000):
    file.write(f"fun f{i}:\n")
    for i in range(1000):
        file.write(f"  if true: if true: if true: pass\n")
file.close()