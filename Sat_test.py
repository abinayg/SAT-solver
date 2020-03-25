
from sat_solver import SAT_solver

x=SAT_solver()							#instantiates the class
# x.expr('(a&~b&~c) | (~a&b&~c)| (~a&~b&c) | (a&b&c) | (d&~e) | (~d&e)')	# takes in the expression

x.expr('(a&b&c) | (b&~b)')

# x.expr('(a&~a) | (b&~b)')

# x.expr('(a) | (~b)')



# x.expr('(a&~a) | (b&~b)')

print("CNF FORM: "+str(x.CNF()))


x.solve(input_dict={})

# print(x.isequivalent('(a^b^c) | (d^e)'))
