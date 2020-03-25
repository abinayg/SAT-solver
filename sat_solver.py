import re
import random

# SAT SOLVER CLASS TO FIND OUT THE INPUT VARIABLE ASSIGNMENT THAT MAKES THE FUNCTION SATISFIABLE

class SAT_solver:
	variables=''						# list of variables in the form of a string
	and_terms=[]						# this will store all the 'AND' terms
	refined_expr=''						# Contains the refined expression
	re_expr=''							# dummy variable used for refining the expression
	wire_list=[]						# contains the wire_names of each output eg.,['x1','x2',....] based on the number of and gates
	clause_list=[]						# contains the clauses of the CNF form
	unit_list=[]
	variable_list=[]
	eval_terms=[]
	output_variable='z'
	unsat=0

	def expr(self,expression):				# takes the expression and finds out the input variables
		self.expression=expression
		f=filter(str.isalnum,self.expression)
		dum=sorted(set("".join(f)))
		self.var_list=dum
		var="".join(dum)
		self.variables=var
		 												# for the storage of the variabl

		#### REFINING THE EXPRESSION

		self.re_expr=self.expression.replace(" ","")
		pattern=re.compile(r'\|')
		matches=pattern.finditer(self.re_expr)
		x=[]
		for match in matches:
			x.append(match.span())

		for i in range(len(x)):
			if i==0:
				sli=0
				self.and_terms.append(self.re_expr[:x[0][0]])
				self.eval_terms.append(self.re_expr[:x[0][0]])
			else:

				self.and_terms.append(self.re_expr[x[sli][1]:x[sli+1][0]])
				self.eval_terms.append(self.re_expr[x[sli][1]:x[sli+1][0]])
				sli+=1
		self.and_terms.append(self.re_expr[x[sli][1]:])
		self.eval_terms.append(self.re_expr[x[sli][1]:])
		imp_var=[]

		k=[]
		self.dummy_and_term=[]
		for i in range(len(self.and_terms)):
			imp_var.append(self.and_terms[i].replace("&",""))
			self.dummy_and_term.append(self.and_terms[i].replace("&",""))
			self.and_terms[i]="AND"+str(self.and_terms[i].replace("&",","))

			imp_var[i]=re.findall(r'[a-z*]',imp_var[i])


		list_min=imp_var[0]
		x=len(imp_var[0])
		index=0
		for i in imp_var:
			if(len(i)<x):
				list_min=i
				index=imp_var.index(i)
		# print(self.dummy_and_term)

		x=self.dummy_and_term[index].replace("(","").replace(")","")


		y=re.findall(r'[a-z]',x)

		self.min_lit_dict={}


		i=0
		while(i<len(x)):
			if(x[i]=='~'):
				self.min_lit_dict[x[i+1]]=0
				i+=2
			else:
				self.min_lit_dict[x[i]]=1
				i+=1


		# check if there's anykind of (a&~a) which makes equation unsat

		if(len(set(y))==1 and len(y)==2):
			self.min_lit_dict={}





		# WRITING THE REFINED EXPRESSION
		self.refined_expr+='OR('
		for i in range(len(self.and_terms)):
			if i==len(self.and_terms)-1:
				self.refined_expr+=str(self.and_terms[i])+")"
			else:
				self.refined_expr+=str(self.and_terms[i])+", "
		self.wire_list=['x'+str(i) for i in range(1,len(self.and_terms)+1)]

		self.variable_list=[self.variables[i] for i in range(len(self.variables))]
		for i in self.wire_list:
			self.variable_list.append(i)
		self.variable_list=list(set(self.variable_list)^set(self.min_lit_dict.keys()))

		# return None


	def get_refined_expr(self):
		return self.refined_expr
	# def print(self):							# return the expression in original form
	# 	return self.expression
	def express(self):							# returns the expression in refined form
		return self.refined_expr
	def num_AND(self):							# total number of 'AND' terms in the expression
		return len(self.and_terms)
	def num_OR(self):							# number of 'OR' terms in the expression
		return len(self.and_terms)-1

	def get_variables(self):					# extracts what are the input variables present in the expression
		return self.variables

	# def get_f(self,inputs):					#### ignore this
	# 	for i in range(len(self.var_list)):
	# 		self.var_storage[self.var_list[i]]=inputs[i]
	# 	return eval(self.expression,self.var_storage)

	def num_variables(self):					# gives the total number of input variables
		return len(self.var_list)

	def CNF(self):								#computes the CNF form
		out_1=''
		out_2=''
		#### change this variable according to the user input
		CNF_LIST=[]
		clause_list=[]

		for i in range(len(self.and_terms)):
			y=self.and_terms[i]
			z=y[y.find("(")+1:y.find(")")]
			z=z.replace(",","")
			### AND (PRODUCT TERMS)
			a=0

			while(a<len(z)):
				if(z[a]=='~'):
					CNF_LIST.append(str('~'+str(self.wire_list[i])+"+"+str(z[a])+str(z[a+1])))
					x1='(~'+str(self.wire_list[i])+"+"+str(z[a])+str(z[a+1])+")"
					out_1+=x1
					a+=2
					self.clause_list.append(x1.replace("+","|").replace("~","not "))
				else:
					CNF_LIST.append(str('~'+str(self.wire_list[i])+"+"+str(z[a])))
					x2='(~'+str(self.wire_list[i])+"+"+str(z[a])+")"
					out_2+=x2
					a+=1
					self.clause_list.append(x2.replace("~","not ").replace("+","|"))
			#### AND (SUMMATION TERM)
			b=0
			k='('+str(self.wire_list[i])+"+"
			while(b<len(z)):
				if(b==len(z)-1):

					k+="~"+z[b]+")"
					break
				if(z[b]=='~'):
					if(b+1==len(z)-1):
						k+=z[b+1]+")"
					else:
						k+=z[b+1]+"+"
					b+=2
				else:
					k+="~"+z[b]+"+"
					b+=1
			out_2+=k
			self.clause_list.append(k.replace("~","not ").replace("+","|"))

		### REFINING THE SUMMATION TERM FOR STORING CNF VARIABLES

		### OR CNF (PRODUCT TERMS)
		out_3=''
		a=0
		while(a<len(self.wire_list)):
			CNF_LIST.append(str(self.output_variable+"+"+"~"+str(self.wire_list[a])))
			x3='('+self.output_variable+"+"+"~"+str(self.wire_list[a])+")"
			out_3+=x3
			a+=1
			self.clause_list.append(x3.replace("~","not ").replace("+","|"))

		### OR CNF (SUMMATION TERM)
		out_4='('+"~"+self.output_variable
		a=0
		while(a<len(self.wire_list)):
			if(a==len(self.wire_list)-1):
				out_4+="+"+str(self.wire_list[a])+")"
			else:
				out_4+="+"+str(self.wire_list[a])
			a+=1
		self.clause_list.append(out_4.replace("~","not ").replace("+","|"))
		self.CNF=out_1+out_2+out_3+out_4
		return self.CNF

	def get_clause_list(self):			#returns the clause_list containing all the CNF clauses
		return self.clause_list


	def assign(self,clause_list,var_dict):		# take the dict value
		for k,val in zip(var_dict.keys(),var_dict.values()):
			for i in range(len(clause_list)):
					if(k[0]=='x'):
						a=2
					else:
						a=1
					x=clause_list[i].find(k)
					if(x!=-1):
						y=clause_list[i].find("not")
						if(x-y==4 and y!=-1):
							a1=clause_list[i][:y]
							b1=clause_list[i][x+a:]

							if(val==1):
								clause_list[i]=a1+"0"+b1
							else:
								clause_list[i]=a1+"1"+b1
						else:
							a1=clause_list[i][:x]
							b1=clause_list[i][x+a:]

							clause_list[i]=a1+str(val)+b1

		return clause_list
	def boolean_algebra(self,clause_list):
		pop_list=[]
		for i in range(len(clause_list)):
			x=clause_list[i].find('1')
			if(x!=-1):
				y=clause_list[i].find('x')
				if(x-y!=1):
					pop_list.append(clause_list[i])

			if(clause_list[i].find('not 0')!=-1):
				pop_list.append(clause_list[i])

			if(clause_list[i].find('not 1')!=-1):
				clause_list[i].replace("not 1","0")


		clause_list=list(set(clause_list)^set(pop_list))


		return clause_list
	def check_zero(self,clause_list):
		for i in range(len(clause_list)):
			a=0
			matches=re.finditer(r'\|',str(clause_list[i]))
			temp_list=[int(match.span()[0]) for match in matches]

			for j in range(len(temp_list)):
				if(j==len(temp_list)-1):
					if(clause_list[i][temp_list[j]+1]=='0'):
						a+=1

				if(clause_list[i][temp_list[j]-1]=='0'):
					a+=1
			if(len(temp_list)+1==a):
				return True

		return False
	def find_unit_clauses(self,clause_list):
		unit_clause=[]
		for i in range(len(clause_list)):
			a=0
			matches=re.finditer(r'\|',str(clause_list[i]))
			temp_list=[int(match.span()[0]) for match in matches]

			for j in range(len(temp_list)):
				if(j==len(temp_list)-1):
					if(clause_list[i][temp_list[j]+1]=='0'):
						a+=1

				if(clause_list[i][temp_list[j]-1]=='0'):
					a+=1
			x=bool(re.search('[a-zA-Z]',clause_list[i]))

			if(len(temp_list)==a and x==True):
				unit_clause.append(clause_list[i])

		return unit_clause
	def unit_clause_assignment(self,unit_list,unit_dict):
		for i in unit_list:
			x=re.findall(r'[a-z].',i)
			y=x[-1].replace(")","").replace("|","")
			if(len(x)>1):
				unit_dict[y]=0
			else:
				unit_dict[y]=1
		return unit_dict

	def solve_z(self,clause_list):
		clause_list=self.assign(clause_list,var_dict={'z':1})
		return self.boolean_algebra(clause_list)
	def solve_min_list(self,clause_list,min_dict):
		clause_list=self.assign(clause_list,min_dict)
		return self.boolean_algebra(clause_list)


	def solve(self,input_dict):							#### BACKTRACKING ALGORITHM IMPLEMENTATION
	# print(var_dict)
		q=0
		variable_list=self.variable_list
		if(input_dict!={}):

			for i in range(len(self.eval_terms)):
				try:
					if(eval(self.eval_terms[i],input_dict)):
						q=1
						break
				except:
					pass
			if(q==1):
				print("HOLA.! SAT for the assignment")
			else:
				print("UNSAT for the user assignment")

		dummy=self.clause_list

		self.final_assignment={}
		self.variable_assignments={}
		self.final_assignment['z']=1
		count=0

		solve_z=self.solve_z(dummy)
		removed_list=[]
		# print("min_lit_dict: "+str(self.min_lit_dict))

		if(self.min_lit_dict!={}):
			# print("Found some min_lit_dict.!")
			dummy=self.solve_min_list(solve_z,self.min_lit_dict)
			for i in self.min_lit_dict.items():
				self.final_assignment[i[0]]=i[1]
				self.variable_assignments[i[0]]=i[1]
				removed_list.append(i[0])
				variable_list.remove(i[0])


		unit_dict={}
		# print("variable_list:" +str(self.variable_list))
		# print("min_lit_list: "+str(self.min_lit_list))
		
		last_used=dummy
		while(dummy!=[]):
			# print("Dummy: "+str(dummy))


			unit_list=self.find_unit_clauses(dummy)
			# print("UNIT_clause_LIST"+str(unit_list))

			unit_dict=self.unit_clause_assignment(unit_list,unit_dict)

			# print("UNIT DICT: "+str(unit_dict))
			if(unit_dict=={}):
				if(variable_list==[]):
					break

				if(variable_list!=[]):
					# count=1
					(x,y)=(random.choice(self.variable_list),random.randint(0,1))
					print("Using from variable_list: "+str(x)+": "+str(y))
					# print("picking from the variable_list:"+str(x))
					dummy=self.assign(dummy,{x:y})
					variable_list.remove(x)

					if(x in self.variables):
						self.variable_assignments[x]=y


			if(unit_dict!={}):

				(x,y)=(random.choice(list(unit_dict.items())))
				print("Using from unit_dict: "+str(x)+": "+str(y))
				if(x in variable_list):
					variable_list.remove(x)
				dummy=self.assign(dummy,{x:y})
				# self.final_assignment[x]=y
				# removed_list.append(x)
				# print("The previous unit dict: "+str(prev_var)+": "+str(prev_val))

				del unit_dict[x]

			removed_list.append(x)

			if(x in self.variables):
				self.variable_assignments[x]=y



			zeros=self.check_zero(dummy)
			if(zeros==True):
				for i in removed_list:
					variable_list.append(i)
				removed_list=[]
				dummy=solve_z


			if(zeros==False):
				last_used=dummy


			dummy=self.boolean_algebra(dummy)
			print("Dummy: "+str(dummy))
			print("Removed_list: "+str(removed_list))


		a=None
		print(self.variable_assignments)
		for i in self.eval_terms:
			k=eval(i,self.variable_assignments)
			if(k==1):
				print("\nSATISFIABLE!")
				return self.variable_assignments
				
		print("Unsatisfiable.!")
		return None


	def isequivalent(self,term):
		k=self.variable_assignments
		x=eval(term,k)
		return x

