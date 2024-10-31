for x in {2..20}; do {echo "Starting script $x"; python3 ./ECCML_simulations.py $x 2>&1; echo "Finish, I sleep for a few seconds; sleep 10; echo "done";} done
