import random

# Read in full password bank.
with open('passwords.txt') as f:
    content = f.readlines()

# Strip whitespace.
content = [x.strip() for x in content] 

# Shuffle up array to take random sample.
random.shuffle(content)

# Output specified amount of random lines.
output_file = open('one_hundred_thousand.txt', 'w')
for i in range(0, 110000):
    output_file.write(content[i] + '\n')
output_file.close() 
