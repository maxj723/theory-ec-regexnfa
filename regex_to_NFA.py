from graphviz import Digraph
import argparse

# Get unique names for state
def state_generator(prefix='S'):
    count = 0
    while True:
        yield f"{prefix}{count}"
        count += 1

# Make state generator global for constant use from all functions
global_state_gen = state_generator()

def get_new_state(prefix='S'):
    return next(global_state_gen)

class NFA:
    def __init__(self, Q=None, delta=None, q0=None, F=None):
        self.Q = Q if Q else set()
        self.delta = delta if delta else set()
        self.q0 = q0
        self.F = F if F else set()
    
    def __str__(self):
        result = f"States: {self.Q}\n"
        result += f"Start state: {self.q0}\n"
        result += f"Accept states: {self.F}\n"
        result += "Transitions:\n"
        for (src, symbol, dst) in self.delta:
            result += f"  {src} --{symbol}--> {dst}\n"
        return result

r_counter = {}  # Track instances of each R-NFA
# Count how many R states to get unique
def get_r_count(r_symbol):
    if r_symbol not in r_counter:
        r_counter[r_symbol] = 0
    count = r_counter[r_symbol]
    r_counter[r_symbol] += 1
    return count

# makes basic NFA from R language. makes R-states unique by adding number at end
def create_nfa(symbol):
    if symbol.startswith('R'):
        # Get unique instance number for this R-NFA
        instance = get_r_count(symbol)
        # Create unique names using instance number
        start = f"{symbol}_{instance}_start"
        accept = f"{symbol}_{instance}_accept"
    else:
        start = get_new_state('S')
        accept = get_new_state('A')
    
    Q = {start, accept}
    delta = {(start, symbol, accept)}
    F = {accept}
    return NFA(Q=Q, delta=delta, q0=start, F=F)

# Rename NFAs to create unique states 
def rename_nfa(nfa):
    state_map = {}
    for state in nfa.Q:
        # Check if it's an R-state
        
        if 'R' in state:
            state_map[state] = state
        else:
            new_state = get_new_state('S')
            state_map[state] = new_state
    
    new_Q = set(state_map.values())
    new_delta = set()
    for (src, symbol, dst) in nfa.delta:
        new_src = state_map[src]
        new_dst = state_map[dst]
        new_delta.add((new_src, symbol, new_dst))
    
    new_q0 = state_map[nfa.q0]
    new_F = set(state_map[accept] for accept in nfa.F)
    
    return NFA(Q=new_Q, delta=new_delta, q0=new_q0, F=new_F)

# Concatenate two nfas as done in class
def concat(nfa1, nfa2):
    # Rename nfa2 to ensure unique state names
    nfa2_renamed = rename_nfa(nfa2)
    
    new_Q = nfa1.Q | nfa2_renamed.Q
    new_delta = nfa1.delta | nfa2_renamed.delta
    
    # Add ε-transitions from every accept state of nfa1 to the start state of nfa2_renamed
    for accept in nfa1.F:
        new_delta.add((accept, 'ε', nfa2_renamed.q0))
    
    return NFA(
        Q=new_Q,
        delta=new_delta,
        q0=nfa1.q0,
        F=nfa2_renamed.F
    )

# Get union of two NFAs as done in class w/ new start state
def union_nfa(nfa1, nfa2):
    # Rename both NFAs to ensure unique state names
    nfa1_renamed = rename_nfa(nfa1)
    nfa2_renamed = rename_nfa(nfa2)
    
    new_start = get_new_state('S')
    new_Q = nfa1_renamed.Q | nfa2_renamed.Q | {new_start}
    new_delta = nfa1_renamed.delta | nfa2_renamed.delta
    
    # Add ε-transitions from new start to both nfa1_renamed and nfa2_renamed start states
    new_delta.add((new_start, 'ε', nfa1_renamed.q0))
    new_delta.add((new_start, 'ε', nfa2_renamed.q0))
    
    new_F = nfa1_renamed.F | nfa2_renamed.F
    
    return NFA(
        Q=new_Q,
        delta=new_delta,
        q0=new_start,
        F=new_F
    )

# Apply kleene star to NFA as done in class (new accept state -> NFA -> original start)
def kleene_star(nfa):
    # Rename the NFA to ensure unique state names
    nfa_renamed = rename_nfa(nfa)
    
    new_start = get_new_state('S')
    new_F = nfa_renamed.F | {new_start}
    new_Q = nfa_renamed.Q | {new_start}
    new_delta = nfa_renamed.delta.copy()
    
    # Add ε-transitions from original accept states back to original start
    for accept in new_F:
        new_delta.add((accept, 'ε', nfa_renamed.q0))
    
    return NFA(
        Q=new_Q,
        delta=new_delta,
        q0=new_start,
        F=new_F
    )

# Make deep copy of NFA
def make_nfa_copy(nfa):
    state_map = {}
    
    # Iterate through states. Make new names for states
    for state in nfa.Q:
        if 'R' in state:
            old_instance = state.split('_')[1]
            new_instance = str(int(old_instance) + 1)
            new_state = state.replace(f"_{old_instance}_", f"_{new_instance}_")
            state_map[state] = new_state
        else:
            new_state = get_new_state('S')
            state_map[state] = new_state
    
    # Create new NFA with mapped states
    new_Q = set(state_map.values())
    new_delta = set()
    for (src, symbol, dst) in nfa.delta:
        new_src = state_map[src]
        new_dst = state_map[dst]
        new_delta.add((new_src, symbol, new_dst))
    
    new_q0 = state_map[nfa.q0]
    new_F = set(state_map[accept] for accept in nfa.F)
    
    return NFA(Q=new_Q, delta=new_delta, q0=new_q0, F=new_F)

# Apply kleene plus to NFA as done in class (NFA -> NFA*)
def kleene_plus(nfa):
    # Make a complete copy of the NFA for the star part
    nfa_copy = make_nfa_copy(nfa)
    
    # Create the star NFA from the copy
    star_nfa = kleene_star(nfa_copy)
    
    # Concatenate original with star
    return concat(nfa, star_nfa)

# Make sure only one accept state
def clean_accept_states(nfa):
    new_accept = get_new_state('S')
    new_F = {new_accept}
    new_Q = nfa.Q | {new_accept}
    new_delta = nfa.delta.copy()

    for accept in nfa.F:
        new_delta.add((accept, 'ε', new_accept))

    return NFA(
        Q=new_Q,
        delta=new_delta,
        q0=nfa.q0,
        F=new_F
    )

# Convert regex to postfix so that it can be read by stack
def to_postfix(regex):
    # Initate priority so that postfix is done correctly
    precedence = {'U': 1, '.': 2, '*': 3, '+': 3}
    output = []
    stack = []
    i = 0
    while i < len(regex):
        c = regex[i]
        if c == '(':
            stack.append(c)
            i += 1
        elif c == ')':
            while stack and stack[-1] != '(':
                output.append(stack.pop())
            if not stack:
                raise ValueError("Mismatched parentheses")
            stack.pop()  # Remove '('
            i += 1
        elif c in precedence:
            while (stack and stack[-1] != '(' and
                   precedence.get(stack[-1], 0) >= precedence[c]):
                output.append(stack.pop())
            stack.append(c)
            i += 1
        else:
            # Handle symbols
            symbol = []
            while i < len(regex) and regex[i] not in precedence and regex[i] not in {'(', ')'}:
                symbol.append(regex[i])
                i += 1
            output.append(''.join(symbol))
    while stack:
        # Check for parenthesis and exit if invalid format
        if stack[-1] == '(' or stack[-1] == ')':
            raise ValueError("Mismatched parentheses")
        output.append(stack.pop())
    return output

# Parse the regex to an NFA
def parse_regex(regex):
    # Convert regex to postfix for stack reading
    postfix = to_postfix(regex)
    print(postfix)
    # Parse postfix to NFA
    stack = []
    # Iterate through postfix
    for token in postfix:

        # If token is NFA => Convert to NFA and push to stack
        if token not in {'U', '.', '*', '+'}:
            nfa = create_nfa(token)
            stack.append(nfa)
            print(f"Pushed NFA for symbol '{token}'")

        # If concatenation => append NFAnew = NFA1 . NFA2
        elif token == '.':
            # Concatenation
            nfa2 = stack.pop()
            nfa1 = stack.pop()
            concatenated = concat(nfa1, nfa2)
            stack.append(concatenated)
            print(f"Applied Concatenation: '{nfa1.q0}' . '{nfa2.q0}'")

        # If Union => append NFAnew = NFA1 U NFA2
        elif token == 'U':
            nfa2 = stack.pop()
            nfa1 = stack.pop()
            unioned = union_nfa(nfa1, nfa2)
            stack.append(unioned)
            print(f"Applied Union: '{nfa1.q0}' U '{nfa2.q0}'")

        # If star => append NFAnew = NFA*
        elif token == '*':
            nfa = stack.pop()
            starred = kleene_star(nfa)
            stack.append(starred)
            print(f"Applied Kleene Star on '{nfa.q0}'")

        # if plus => append NFAnew = NFA+
        elif token == '+':
            nfa = stack.pop()
            plus = kleene_plus(nfa)
            stack.append(plus)
            print(f"Applied Kleene Plus on '{nfa.q0}'")
    

    if len(stack) != 1:
        raise ValueError("Invalid regex: Stack has multiple NFAs after parsing.")
    
    final_nfa = stack.pop()

    one_accept_nfa = clean_accept_states(final_nfa)
    print("\nFinal NFA:")
    print(one_accept_nfa)
    return one_accept_nfa

# use graphviz to visualize NFA
def visualize_nfa(nfa, filename):
    dot = Digraph(comment='NFA')
    
    for state in nfa.Q:
        attrs = {'shape': 'doublecircle' if state in nfa.F else 'circle'}
        
        # Update R-state to make easily visible
        if 'R' in state:
            attrs['color'] = 'blue'
            attrs['style'] = 'filled'
            attrs['fillcolor'] = 'lightblue'
            attrs['label'] = state
        
        dot.node(state, **attrs)
    
    # Add start arrow
    dot.node('start', shape='none', label='')
    dot.edge('start', nfa.q0)
    
    # Add transitions with different styles for ε-transitions
    for (src, symbol, dst) in nfa.delta:
        edge_attrs = {}
        if symbol == 'ε':
            edge_attrs['style'] = 'dashed'
            edge_attrs['color'] = 'red'
        dot.edge(src, dst, label=symbol, **edge_attrs)
    
    dot.render(filename, view=True, format='png')

def __main__():
    # use argparse to get cmd line argument
    parser = argparse.ArgumentParser()
    parser.add_argument('regex', type=str)
    args = parser.parse_args()

    nfa = parse_regex(args.regex)
    visualize_nfa(nfa, f'{args.regex}_NFA')

if __name__ == "__main__":
    __main__()