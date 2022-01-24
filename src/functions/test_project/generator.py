import random
file = open("root/module.mf", "w")
for i in range(100000):
    file.write(f"fun f{i}:\n")
    for i in range(10):
        file.write(f"  call(call(call(a, b)))\n")
file.close()