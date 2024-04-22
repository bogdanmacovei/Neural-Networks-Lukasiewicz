import numpy as np
import pandas as pd
from keras.models import Sequential
from keras.layers import Dense, Activation
from keras.utils.generic_utils import get_custom_objects
from keras import backend as K

input_dim = 2
output_dim = 1

df = pd.read_csv("train.csv")
X = np.array(df[['x', 'y']])
y = np.array(df['f'])

def relu_1(x):
    return K.minimum(K.maximum(0.0, x), 1.0)

model = Sequential()
model.add(Dense(4, input_dim=input_dim, activation=relu_1, kernel_initializer='RandomNormal'))
model.add(Dense(6, input_dim=input_dim, activation=relu_1))
model.add(Dense(2, activation=relu_1))
model.add(Dense(output_dim, activation=relu_1))

model.compile(loss='mse', optimizer='sgd')
model.fit(X, y, epochs=100, batch_size=1, verbose=1)

