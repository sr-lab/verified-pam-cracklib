import json

def import_json(path):
    """Decodes and returns the JSON object in the file at the specified path.
	
    Args:
        path (str): The path of the file to read.
		
    """
    with open(path) as data_file:    
        return json.load(data_file)
        
# Import all files.
results_v = import_json('results_v.json')['runs']
results_nodict = import_json('results_nodict.json')['runs']
results_nodict_mcr = import_json('results_nodict_mcr.json')['runs']
results_nodict_mcr_fixed = import_json('results_nodict_mcr_fixed.json')['runs']
results_v_mcr = import_json('results_v_mcr.json')['runs']
results_v_basic16 = import_json('results_v_basic16.json')['runs']

# Produce CSV.
results = "Password, Default, Default T, HAPSL, HAPSL T, MCR, MCR T, MCR (fixed), MCR (fixed) T, MCR (HAPSL), MCR (HAPSL) T, Basic16, Basic16 T\n"
for i in range(0, 100000):
    results += results_v[i]['password']
    results += ", "
    results += str(results_nodict[i]['valid'])
    results += ", "
    results += str(results_nodict[i]['time'])
    results += ", "
    results += str(results_v[i]['valid'])
    results += ", "
    results += str(results_v[i]['time'])
    results += ", "
    results += str(results_nodict_mcr[i]['valid'])
    results += ", "
    results += str(results_nodict_mcr[i]['time'])
    results += ", "
    results += str(results_nodict_mcr_fixed[i]['valid'])
    results += ", "
    results += str(results_nodict_mcr_fixed[i]['time'])
    results += ", "
    results += str(results_v_mcr[i]['valid'])
    results += ", "
    results += str(results_v_mcr[i]['time'])
    results += ", "
    results += str(results_v_basic16[i]['valid'])
    results += ", "
    results += str(results_v_basic16[i]['time'])
    results += "\n"

# Write CSV out.    
open('results.csv', 'w').write(results)
