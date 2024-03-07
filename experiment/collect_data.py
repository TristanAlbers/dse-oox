import numpy as np
import pandas as pd
import os

def main():
    file = 'benchmark_minepump'
    df = pd.read_csv(f"{file}", delimiter=',')

    # print(f"{len(df['name'].unique())} mutations checked")
    # df = df[df['result'] != 'VALID']
    df = df.filter(items=['name', 'time', 'result', 'coverage_tuples', 'concolic_invocations', 'paths explored'])
    # print(df)

    # Group on name and heuristic, average the execution time
    # df = df.groupby(['name', 'heuristic'], as_index=False).agg("mean")



    # df = df.sort_values(by=['name', 'heuristic'])
    df = df.sort_values(by=['name'])
    # df = df.filter(items=['heuristic', 'time'])

    # print(df)

    latex_table = df.to_latex(
    index=False,  # To not include the DataFrame index as a column in the table
    caption="Results ",  # The caption to appear above the table in the LaTeX document
    label="tab:res",  # A label used for referencing the table within the LaTeX document
    position="h",  # The preferred positions where the table should be placed in the document ('here', 'top', 'bottom', 'page')
    column_format="c|c|c|c|c|c",  # The format of the columns: left-aligned with vertical lines between them
    escape=True,  # Disable escaping LaTeX special characters in the DataFrame
    float_format="{:0.3f}".format  # Formats floats to two decimal places
    )

    print(latex_table)
    
    with open('generated_files\\latex-table-minepump', 'w') as f:
        f.write(latex_table)

    '''
    # Pivot the table into one like this, with each row a mutation's execution time
    #     |DFS |M2DU|RandomPath|RoundRobin|
    # time| .. | .. | ..       | ..       |
    df = df.assign(idx=df.groupby('heuristic').cumcount())
    df = df.pivot(index='idx', columns='heuristic', values='time')

    print(f"{len(df)} invalid mutations found")

    df.columns = ['MD2U', 'Concolic']
    
    ax = df.plot.box()
    ax.set_ylabel('time (s)')

    ax.figure.savefig(f'{file}_picture')'''

main()