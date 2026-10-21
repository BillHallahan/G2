import os

failed = 0
timeouts = 0
time = 0
t_prop = 0
error_p = 0

def extract_number(s):
    try:
        return round(float(s.rstrip("s")), 2)
    except ValueError:
        return None

def readNebula(file):
    contents = open(file)
    global t_prop, time, failed, timeouts, error_p
    for lne in (contents.readlines()[1:]):
        t_prop += 1
        lne_pieces = lne.split(",")
        prop = lne_pieces[0]
        outcome = lne_pieces[4]
        maybeTime = extract_number(lne_pieces[5])

        if outcome == "Failed":
            time += maybeTime
            failed += 1
        elif outcome == "Timeout":
            timeouts += 1
        elif outcome == "Verified":
            print("Error: Prop is verified" + prop)
        else:
            error_p += 1
            print("ERROR")


def main():
    global t_prop, time, failed, timeouts, error_p

    setpath = "/Users/abhachaudhary/Downloads/ZenoCounter"
    csv_files = os.listdir(setpath)

    for csv_file in csv_files:
        
        csv_path = os.path.join(setpath, csv_file)
        if os.path.isfile(csv_path):
            print("Reading the data for File: " + csv_file)
            readNebula(csv_path)

    print("Total number of props: " + str(t_prop))
    avg_time = round(time/failed, 2)
    print("Average time to refute a property: " + str(avg_time))
    print("Total number of props, Nebula found Cex: " + str(failed))
    print("Total number of timeouts: " + str(timeouts))
    print("Number of props that errored: " + str(error_p))


if __name__ == "__main__":
    main()